"""Hierarchical modular DAG clustering (chapters -> sections) with exact formal interfaces."""

from __future__ import annotations

import json
import math
import re
import sqlite3
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from proof_compressor.schema import connect_db, get_meta, set_meta

_CAMEL_SPLIT_1 = re.compile(r"([a-z0-9])([A-Z])")
_CAMEL_SPLIT_2 = re.compile(r"([A-Z]+)([A-Z][a-z])")
_THM_KINDS = frozenset({"theorem", "lemma"})


@dataclass
class ClusterReport:
    """Summary of hierarchical chapter/section clustering and interface widths."""

    total_declarations: int = 0
    total_loc: int = 0
    chapter_count: int = 0
    section_count: int = 0
    total_cross_chapter_edges: int = 0
    total_internal_chapter_edges: int = 0
    internal_edge_ratio: float = 0.0
    chapters: list[dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _open_db(db: sqlite3.Connection | str | Path) -> tuple[sqlite3.Connection, bool]:
    if isinstance(db, sqlite3.Connection):
        return db, False
    return connect_db(db), True


def _clean_module_parts(path: str) -> list[str]:
    p = (path or "").strip().replace("\\", "/")
    while p.startswith("./"):
        p = p[2:]
    for prefix in ("lean/src/", "src/"):
        if p.startswith(prefix):
            p = p[len(prefix) :]
            break
    if p.endswith(".lean"):
        p = p[:-5]
    if "/" in p:
        parts = [seg for seg in p.split("/") if seg]
    else:
        parts = [seg for seg in p.split(".") if seg]
    return parts or ["Root"]


def _humanize_token(tok: str) -> str:
    s = tok.replace("_", " ").replace("-", " ")
    s = _CAMEL_SPLIT_2.sub(r"\1 \2", s)
    s = _CAMEL_SPLIT_1.sub(r"\1 \2", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s or tok


def _format_cluster_title(prefix_parts: tuple[str, ...], top_decl_short: str | None = None) -> str:
    meaningful = [p for p in prefix_parts if p not in ("Root", "src", "lean")]
    if not meaningful:
        base = "Core Foundations"
    else:
        # Use up to last 2 meaningful segments for crisp titles
        tail = meaningful[-2:] if len(meaningful) >= 2 else meaningful
        base = " / ".join(_humanize_token(p) for p in tail)
    if top_decl_short and len(base) < 42:
        clean_top = _humanize_token(top_decl_short)
        if clean_top.lower() not in base.lower() and len(clean_top) <= 36:
            return f"{base}: {clean_top}"
    return base


def _topo_order_groups(
    group_ids: list[int],
    dir_deps: dict[tuple[int, int], int],
    mean_dom_depth: dict[int, float],
    has_root: set[int],
) -> list[int]:
    """Order groups from foundational prerequisites to main-theorem consumers.

    `dir_deps[(a, b)]` is the number of edges where `a` depends on `b`, so `b`
    should precede `a` in reading order. Cycles are broken deterministically via
    minimum unresolved dependency weight, deepest dominator depth, and non-root first.
    """
    remaining = set(group_ids)
    ordered: list[int] = []

    out_w: dict[int, Counter[int]] = {g: Counter() for g in group_ids}
    in_w: dict[int, Counter[int]] = {g: Counter() for g in group_ids}
    for (a, b), w in dir_deps.items():
        if a != b and a in remaining and b in remaining and w > 0:
            out_w[a][b] += w
            in_w[b][a] += w

    while remaining:
        # Candidates with zero remaining prerequisite dependencies
        ready = [g for g in remaining if sum(out_w[g].values()) == 0]
        if ready:
            # Prefer non-root foundational groups with deeper dominator depth first
            ready.sort(
                key=lambda g: (
                    1 if g in has_root else 0,
                    -mean_dom_depth.get(g, 0.0),
                    -sum(in_w[g].values()),
                    g,
                )
            )
            pick = ready[0]
        else:
            # Feedback-arc tie-breaker: fewest unresolved outgoing deps relative to incoming consumers
            pick = min(
                remaining,
                key=lambda g: (
                    1 if g in has_root else 0,
                    sum(out_w[g].values()) / (1.0 + sum(in_w[g].values())),
                    -mean_dom_depth.get(g, 0.0),
                    g,
                ),
            )
        ordered.append(pick)
        remaining.remove(pick)
        for dependent in list(in_w[pick].keys()):
            if dependent in remaining:
                out_w[dependent].pop(pick, None)
        for prereq in list(out_w[pick].keys()):
            if prereq in remaining:
                in_w[prereq].pop(pick, None)

    return ordered


def _shared_prefix_len(a: tuple[str, ...], b: tuple[str, ...]) -> int:
    k = 0
    for xa, xb in zip(a, b):
        if xa != xb:
            break
        k += 1
    return k


def _common_prefix(prefixes: list[tuple[str, ...]]) -> tuple[str, ...]:
    if not prefixes:
        return ("Root",)
    # First compute exact longest common prefix across all sections
    cur = list(prefixes[0])
    for p in prefixes[1:]:
        n = _shared_prefix_len(tuple(cur), p)
        cur = cur[:n]
        if not cur:
            break
    if cur:
        return tuple(cur)
    # Otherwise use the most common top-2 prefix weighted by frequency
    counts = Counter(p[:2] for p in prefixes if p)
    if counts:
        top, freq = counts.most_common(1)[0]
        if freq >= len(prefixes) * 0.5:
            return top
    # Fallback to most common top-1 prefix
    top1 = Counter(p[0] for p in prefixes if p).most_common(1)
    return (top1[0][0],) if top1 else ("Root",)


def cluster_graph(
    db: sqlite3.Connection | str | Path,
    *,
    max_chapters: int = 12,
    max_sections: int = 96,
    max_interface_items: int = 250,
    reachable_only: bool = True,
    batch_size: int = 50_000,
) -> ClusterReport:
    """Partition reachable declarations into hierarchical chapters -> sections with formal interfaces."""
    conn, should_close = _open_db(db)
    try:
        cur = conn.cursor()

        has_reachable = False
        if reachable_only:
            row = cur.execute(
                "SELECT 1 FROM metrics WHERE reachable = 1 LIMIT 1"
            ).fetchone()
            has_reachable = row is not None

        if reachable_only and has_reachable:
            decl_sql = (
                "SELECT d.id, d.name, d.short_name, d.module_id, d.kind, d.type_sig, "
                "d.body_loc, d.is_mathlib, d.is_bookkeeping, COALESCE(mo.path, ''), "
                "COALESCE(m.dominator_depth, 0), COALESCE(m.bottleneck_score, 0.0) "
                "FROM declarations d "
                "JOIN metrics m ON m.decl_id = d.id "
                "LEFT JOIN modules mo ON mo.id = d.module_id "
                "WHERE m.reachable = 1"
            )
        else:
            decl_sql = (
                "SELECT d.id, d.name, d.short_name, d.module_id, d.kind, d.type_sig, "
                "d.body_loc, d.is_mathlib, d.is_bookkeeping, COALESCE(mo.path, ''), "
                "COALESCE(m.dominator_depth, 0), COALESCE(m.bottleneck_score, 0.0) "
                "FROM declarations d "
                "LEFT JOIN metrics m ON m.decl_id = d.id "
                "LEFT JOIN modules mo ON mo.id = d.module_id"
            )

        proj_decls: dict[int, dict[str, Any]] = {}
        all_decl_info: dict[int, dict[str, Any]] = {}
        mod_ids_seen: set[int] = set()

        for (
            did,
            name,
            short_name,
            mid,
            kind,
            type_sig,
            body_loc,
            is_ml,
            is_bk,
            mpath,
            dom_depth,
            bscore,
        ) in cur.execute(decl_sql):
            did_i = int(did)
            info = {
                "id": did_i,
                "name": name or "",
                "short_name": short_name or "",
                "module_id": int(mid or 0),
                "kind": (kind or "").lower(),
                "type_sig": (type_sig or "")[:240],
                "body_loc": max(1, int(body_loc or 0)),
                "is_mathlib": int(is_ml or 0),
                "is_bookkeeping": int(is_bk or 0),
                "module_path": mpath or "",
                "dom_depth": int(dom_depth or 0),
                "bottleneck_score": float(bscore or 0.0),
            }
            all_decl_info[did_i] = info
            if info["is_mathlib"] == 0:
                proj_decls[did_i] = info
                mod_ids_seen.add(info["module_id"])

        # Clear existing clusters before writing fresh hierarchy
        conn.execute("DELETE FROM clusters")
        conn.execute("UPDATE metrics SET cluster_id = NULL")

        if not proj_decls:
            report = ClusterReport()
            set_meta(conn, "analysis_cluster_stats", json.dumps(report.to_dict()))
            conn.commit()
            return report

        # Load root IDs from meta
        root_ids: set[int] = set()
        roots_raw = get_meta(conn, "analysis_roots")
        if roots_raw:
            try:
                for item in json.loads(roots_raw):
                    rid = item.get("id") if isinstance(item, dict) else item
                    if rid in proj_decls:
                        root_ids.add(int(rid))
            except Exception:
                pass

        # Load deduplicated outgoing edges from reachable project declarations
        # (including edges into Mathlib boundary declarations for exact interface_in)
        proj_edges: list[tuple[int, int]] = []  # (src, dst) where both in proj_decls
        ext_ml_edges: list[tuple[int, int]] = []  # (src in proj, dst in mathlib)
        prev_src = -1
        prev_dst = -1
        for src_id, dst_id in cur.execute(
            "SELECT src_id, dst_id FROM edges ORDER BY src_id, dst_id"
        ):
            if src_id == dst_id or (src_id == prev_src and dst_id == prev_dst):
                continue
            prev_src = src_id
            prev_dst = dst_id
            if src_id not in proj_decls:
                continue
            if dst_id in proj_decls:
                proj_edges.append((src_id, dst_id))
            elif dst_id in all_decl_info:
                ext_ml_edges.append((src_id, dst_id))

        # Step 1: Build initial fine atomic units from module hierarchy (or namespaces if 1 module)
        use_namespace = len(mod_ids_seen) <= 1
        raw_groups: dict[tuple[str, ...], list[int]] = defaultdict(list)

        for did, info in proj_decls.items():
            if use_namespace:
                ns_parts = info["name"].split(".")[:-1]
                key = tuple(ns_parts[:2]) if ns_parts else _clean_module_parts(info["module_path"])[:2]
            else:
                parts = _clean_module_parts(info["module_path"])
                # Use up to 3 directory/module levels so huge repos start with manageable sections
                key = tuple(parts[:3]) if len(parts) >= 3 else tuple(parts)
            raw_groups[key].append(did)

        # If we ended up with > max_sections atomic groups, collapse level-3 into level-2 prefixes
        if len(raw_groups) > max_sections:
            collapsed: dict[tuple[str, ...], list[int]] = defaultdict(list)
            for key, dids in raw_groups.items():
                k2 = key[:2] if len(key) >= 2 else key
                collapsed[k2].extend(dids)
            raw_groups = collapsed

        # Assign initial section IDs 0..S-1
        sec_keys = sorted(raw_groups.keys())
        sec_members: dict[int, list[int]] = {i: raw_groups[k] for i, k in enumerate(sec_keys)}
        sec_prefix: dict[int, tuple[str, ...]] = {i: k for i, k in enumerate(sec_keys)}
        decl_to_sec: dict[int, int] = {}
        for sid, dids in sec_members.items():
            for d in dids:
                decl_to_sec[d] = sid

        # Step 2: If still > max_sections, greedily merge smallest sections into best neighbor
        def _build_group_graph(
            decl_to_grp: dict[int, int],
        ) -> tuple[dict[tuple[int, int], int], dict[int, Counter[int]]]:
            dir_w: dict[tuple[int, int], int] = Counter()
            undir_adj: dict[int, Counter[int]] = defaultdict(Counter)
            for u, v in proj_edges:
                gu = decl_to_grp[u]
                gv = decl_to_grp[v]
                if gu != gv:
                    dir_w[(gu, gv)] += 1
                    undir_adj[gu][gv] += 1
                    undir_adj[gv][gu] += 1
            return dir_w, undir_adj

        if len(sec_members) > max_sections:
            _dw, undir_adj = _build_group_graph(decl_to_sec)
            while len(sec_members) > max_sections:
                # Pick smallest section
                smallest = min(sec_members.keys(), key=lambda s: (len(sec_members[s]), s))
                # Pick best neighbor by shared prefix + edge affinity
                nbs = undir_adj.get(smallest)
                best_target: int | None = None
                best_score = -1.0
                p_small = sec_prefix[smallest]
                candidates = list(nbs.keys()) if nbs else [s for s in sec_members if s != smallest]
                for cand in candidates:
                    if cand == smallest or cand not in sec_members:
                        continue
                    ew = nbs[cand] if nbs else 0
                    pref = _shared_prefix_len(p_small, sec_prefix[cand])
                    sc = (ew + 0.5) * (1.0 + 1.5 * pref) / math.sqrt(len(sec_members[cand]) + 1.0)
                    if sc > best_score:
                        best_score = sc
                        best_target = cand
                if best_target is None:
                    break
                # Merge smallest into best_target
                for d in sec_members[smallest]:
                    decl_to_sec[d] = best_target
                sec_members[best_target].extend(sec_members[smallest])
                sec_prefix[best_target] = _common_prefix([sec_prefix[best_target], sec_prefix[smallest]])
                del sec_members[smallest]
                del sec_prefix[smallest]
                # Update undir_adj
                for nb, w in list(undir_adj.get(smallest, {}).items()):
                    if nb != best_target and nb in sec_members:
                        undir_adj[best_target][nb] += w
                        undir_adj[nb][best_target] += w
                    undir_adj[nb].pop(smallest, None)
                undir_adj[best_target].pop(smallest, None)
                undir_adj.pop(smallest, None)

        # Re-index sections cleanly 0..S-1
        active_sec_ids = sorted(sec_members.keys())
        sec_remap = {old: new for new, old in enumerate(active_sec_ids)}
        sec_members = {sec_remap[old]: sec_members[old] for old in active_sec_ids}
        sec_prefix = {sec_remap[old]: sec_prefix[old] for old in active_sec_ids}
        decl_to_sec = {d: sec_remap[s] for d, s in decl_to_sec.items()}
        num_sections = len(sec_members)

        # Step 3: Agglomerate sections into Chapters minimizing cross-cluster interface width
        target_chapters = min(
            max_chapters,
            max(1, min(num_sections, max(3, int(round(math.sqrt(num_sections) * 1.4))))),
        )
        if num_sections <= max_chapters:
            # Still merge tiny orphan sections if there are many small ones
            target_chapters = min(max_chapters, max(1, num_sections))
            if num_sections > 8:
                target_chapters = min(max_chapters, max(4, num_sections // 2))

        # Initialize each chapter with one section
        chap_sections: dict[int, list[int]] = {s: [s] for s in range(num_sections)}
        chap_size: dict[int, int] = {s: len(sec_members[s]) for s in range(num_sections)}
        chap_prefixes: dict[int, list[tuple[str, ...]]] = {s: [sec_prefix[s]] for s in range(num_sections)}
        sec_to_chap: dict[int, int] = {s: s for s in range(num_sections)}

        # Compute exact per-chapter distinct boundary interface declarations between pairs
        pair_boundary_decls: dict[tuple[int, int], set[int]] = defaultdict(set)
        pair_edge_counts: Counter[tuple[int, int]] = Counter()
        for u, v in proj_edges:
            su = decl_to_sec[u]
            sv = decl_to_sec[v]
            if su != sv:
                a, b = (su, sv) if su < sv else (sv, su)
                pair_boundary_decls[(a, b)].add(v)
                pair_edge_counts[(a, b)] += 1

        total_proj = len(proj_decls)
        # Hard chapter size cap scales with target_chapters so no mega-chapter swallows distinct domains
        cap_ratio = max(0.22, min(0.60, 1.8 / max(2, target_chapters)))
        max_chap_cap = max(25, int(total_proj * cap_ratio))

        while len(chap_sections) > target_chapters:
            best_pair: tuple[int, int] | None = None
            best_score = -1.0

            active_chaps = sorted(chap_sections.keys())
            # Evaluate connected pairs first
            candidate_pairs: set[tuple[int, int]] = set(pair_edge_counts.keys())
            # Also include pairs sharing a directory prefix even if sparsely connected
            by_top: dict[str, list[int]] = defaultdict(list)
            for cid in active_chaps:
                pref = _common_prefix(chap_prefixes[cid])
                if pref:
                    by_top[pref[0]].append(cid)
            for grp in by_top.values():
                for i in range(len(grp)):
                    for j in range(i + 1, min(len(grp), i + 12)):
                        a, b = grp[i], grp[j]
                        candidate_pairs.add((a, b) if a < b else (b, a))

            # Strictly prefer pairs whose merged size stays within max_chap_cap
            valid_pairs = [
                (a, b)
                for a, b in candidate_pairs
                if a in chap_sections
                and b in chap_sections
                and (chap_size[a] + chap_size[b]) <= max_chap_cap
            ]

            if valid_pairs:
                for a, b in valid_pairs:
                    iface_red = len(pair_boundary_decls.get((a, b), ()))
                    edges_ab = pair_edge_counts.get((a, b), 0)
                    pa = _common_prefix(chap_prefixes[a])
                    pb = _common_prefix(chap_prefixes[b])
                    sp = _shared_prefix_len(pa, pb)
                    pref_mult = 1.0 + (1.2 if sp >= 2 else (0.5 if sp == 1 else 0.0))
                    denom = math.sqrt(max(1, chap_size[a]) * max(1, chap_size[b]))
                    score = pref_mult * ((2.0 * iface_red + edges_ab + 0.25) / (denom + 2.0))
                    if score > best_score:
                        best_score = score
                        best_pair = (a, b)
            else:
                # Fallback: merge the two smallest chapters that stay under cap (or smallest pair overall)
                active_chaps.sort(key=lambda c: (chap_size[c], c))
                if len(active_chaps) < 2:
                    break
                a, b = active_chaps[0], active_chaps[1]
                if chap_size[a] + chap_size[b] > max_chap_cap and len(chap_sections) <= max_chapters:
                    break
                best_pair = (a, b) if a < b else (b, a)

            if best_pair is None:
                break

            a, b = best_pair
            # Merge b into a
            chap_sections[a].extend(chap_sections[b])
            chap_size[a] += chap_size[b]
            chap_prefixes[a].extend(chap_prefixes[b])
            for s in chap_sections[b]:
                sec_to_chap[s] = a
            del chap_sections[b]
            del chap_size[b]
            del chap_prefixes[b]

            # Update pair_edge_counts & pair_boundary_decls involving b -> a
            pair_edge_counts.pop((a, b), None)
            pair_boundary_decls.pop((a, b), None)
            keys_to_move = [k for k in list(pair_edge_counts.keys()) if b in k]
            for k in keys_to_move:
                other = k[1] if k[0] == b else k[0]
                w = pair_edge_counts.pop(k)
                bset = pair_boundary_decls.pop(k, set())
                if other == a or other not in chap_sections:
                    continue
                nk = (a, other) if a < other else (other, a)
                pair_edge_counts[nk] += w
                pair_boundary_decls[nk].update(bset)

        # Step 4: Fast 1-pass section boundary refinement (move misplaced sections to stronger neighbor)
        if len(chap_sections) > 1:
            sec_to_chap_edges: dict[int, Counter[int]] = defaultdict(Counter)
            for u, v in proj_edges:
                su = decl_to_sec[u]
                sv = decl_to_sec[v]
                if su != sv:
                    sec_to_chap_edges[su][sec_to_chap[sv]] += 1
                    sec_to_chap_edges[sv][sec_to_chap[su]] += 1

            for s in range(num_sections):
                cur_c = sec_to_chap[s]
                if len(chap_sections[cur_c]) <= 1:
                    continue
                c_counts = sec_to_chap_edges.get(s)
                if not c_counts:
                    continue
                cur_aff = c_counts.get(cur_c, 0)
                best_c, best_aff = c_counts.most_common(1)[0]
                if best_c != cur_c and best_aff > max(3, int(cur_aff * 1.8)):
                    # Check balance cap
                    if chap_size[best_c] + len(sec_members[s]) <= max_chap_cap:
                        chap_sections[cur_c].remove(s)
                        chap_size[cur_c] -= len(sec_members[s])
                        chap_sections[best_c].append(s)
                        chap_size[best_c] += len(sec_members[s])
                        sec_to_chap[s] = best_c

        # Step 5: Order chapters and sections topologically (foundations -> root theorem)
        decl_to_chap = {d: sec_to_chap[s] for d, s in decl_to_sec.items()}
        chap_dir_deps, _ = _build_group_graph(decl_to_chap)

        chap_mean_depth: dict[int, float] = {}
        chap_has_root: set[int] = set()
        for cid, sids in chap_sections.items():
            dids = [d for s in sids for d in sec_members[s]]
            chap_mean_depth[cid] = sum(proj_decls[d]["dom_depth"] for d in dids) / max(1, len(dids))
            if any(d in root_ids for d in dids):
                chap_has_root.add(cid)

        ordered_cids = _topo_order_groups(
            list(chap_sections.keys()),
            chap_dir_deps,
            chap_mean_depth,
            chap_has_root,
        )

        sec_dir_deps, _ = _build_group_graph(decl_to_sec)

        # Assign final database IDs: chapters 1..C, sections C+1..C+S
        chap_db_id: dict[int, int] = {cid: i + 1 for i, cid in enumerate(ordered_cids)}
        sec_db_id: dict[int, int] = {}
        next_id = len(ordered_cids) + 1
        ordered_secs_by_chap: dict[int, list[int]] = {}

        for cid in ordered_cids:
            sids = chap_sections[cid]
            s_depth = {
                s: sum(proj_decls[d]["dom_depth"] for d in sec_members[s]) / max(1, len(sec_members[s]))
                for s in sids
            }
            s_root = {s for s in sids if any(d in root_ids for d in sec_members[s])}
            ord_s = _topo_order_groups(sids, sec_dir_deps, s_depth, s_root)
            ordered_secs_by_chap[cid] = ord_s
            for s in ord_s:
                sec_db_id[s] = next_id
                next_id += 1

        decl_final_sec_db: dict[int, int] = {d: sec_db_id[s] for d, s in decl_to_sec.items()}
        decl_final_chap_db: dict[int, int] = {d: chap_db_id[sec_to_chap[s]] for d, s in decl_to_sec.items()}

        # Step 6: Compute exact formal interfaces (interface_in, interface_out) for every chapter & section
        sec_in_refs: dict[int, Counter[int]] = defaultdict(Counter)
        sec_out_refs: dict[int, Counter[int]] = defaultdict(Counter)
        chap_in_refs: dict[int, Counter[int]] = defaultdict(Counter)
        chap_out_refs: dict[int, Counter[int]] = defaultdict(Counter)

        internal_chap_edges = 0
        cross_chap_edges = 0

        for u, v in proj_edges:
            su = decl_final_sec_db[u]
            sv = decl_final_sec_db[v]
            cu = decl_final_chap_db[u]
            cv = decl_final_chap_db[v]
            if su != sv:
                sec_in_refs[su][v] += 1
                sec_out_refs[sv][v] += 1
            if cu != cv:
                cross_chap_edges += 1
                chap_in_refs[cu][v] += 1
                chap_out_refs[cv][v] += 1
            else:
                internal_chap_edges += 1

        # Add Mathlib boundary dependencies to interface_in
        for u, v in ext_ml_edges:
            su = decl_final_sec_db[u]
            cu = decl_final_chap_db[u]
            sec_in_refs[su][v] += 1
            chap_in_refs[cu][v] += 1

        # Root theorems are always part of their section's and chapter's interface_out
        for rid in root_ids:
            sec_out_refs[decl_final_sec_db[rid]][rid] += 1
            chap_out_refs[decl_final_chap_db[rid]][rid] += 1

        def _serialize_interface(ref_counter: Counter[int], is_input: bool) -> list[dict[str, Any]]:
            items: list[tuple[tuple[Any, ...], dict[str, Any]]] = []
            for did, rcnt in ref_counter.items():
                info = all_decl_info.get(did)
                if info is None:
                    continue
                src_cluster = decl_final_sec_db.get(did)
                rec = {
                    "decl_id": did,
                    "name": info["name"],
                    "short_name": info["short_name"],
                    "kind": info["kind"],
                    "type_sig": info["type_sig"],
                    "is_mathlib": info["is_mathlib"],
                    "cluster_id": src_cluster,
                    "ref_count": int(rcnt),
                    "bottleneck_score": info["bottleneck_score"],
                }
                sort_key = (
                    info["is_mathlib"] if is_input else 0,
                    info["is_bookkeeping"],
                    -rcnt,
                    -info["bottleneck_score"],
                    info["name"],
                )
                items.append((sort_key, rec))
            items.sort(key=lambda x: x[0])
            return [rec for _, rec in items[:max_interface_items]]

        def _top_theorem_short(dids: list[int]) -> str | None:
            thms = [
                proj_decls[d]
                for d in dids
                if proj_decls[d]["kind"] in _THM_KINDS and not proj_decls[d]["is_bookkeeping"]
            ]
            pool = thms or [proj_decls[d] for d in dids if not proj_decls[d]["is_bookkeeping"]]
            if not pool:
                return None
            best = max(pool, key=lambda x: (x["bottleneck_score"], x["body_loc"]))
            return best["short_name"] or best["name"].rsplit(".", 1)[-1]

        # Insert clusters (level=0 chapters, level=1 sections)
        cluster_rows: list[tuple[Any, ...]] = []
        chapters_summary: list[dict[str, Any]] = []

        for cid in ordered_cids:
            cdb_id = chap_db_id[cid]
            sids = ordered_secs_by_chap[cid]
            chap_dids = [d for s in sids for d in sec_members[s]]
            chap_loc = sum(proj_decls[d]["body_loc"] for d in chap_dids)
            cpref = _common_prefix([sec_prefix[s] for s in sids])
            ctitle = _format_cluster_title(cpref, _top_theorem_short(chap_dids))

            c_in = _serialize_interface(chap_in_refs[cdb_id], is_input=True)
            c_out = _serialize_interface(chap_out_refs[cdb_id], is_input=False)
            key_exports = [x["short_name"] or x["name"] for x in c_out[:3]]
            csummary = (
                f"{len(chap_dids)} declarations ({chap_loc:,} LOC) across {len(sids)} section(s); "
                f"interface {len(chap_in_refs[cdb_id])} in -> {len(chap_out_refs[cdb_id])} out"
                + (f"; key exports: {', '.join(key_exports)}" if key_exports else "")
            )

            cluster_rows.append(
                (
                    cdb_id,
                    None,
                    0,
                    ctitle,
                    len(chap_dids),
                    chap_loc,
                    json.dumps(c_in),
                    json.dumps(c_out),
                    csummary,
                )
            )

            sec_summaries: list[dict[str, Any]] = []
            for s in sids:
                sdb_id = sec_db_id[s]
                sdids = sec_members[s]
                sloc = sum(proj_decls[d]["body_loc"] for d in sdids)
                stitle = _format_cluster_title(sec_prefix[s], _top_theorem_short(sdids))
                s_in = _serialize_interface(sec_in_refs[sdb_id], is_input=True)
                s_out = _serialize_interface(sec_out_refs[sdb_id], is_input=False)
                s_exports = [x["short_name"] or x["name"] for x in s_out[:3]]
                ssummary = (
                    f"{len(sdids)} declarations ({sloc:,} LOC); "
                    f"interface {len(sec_in_refs[sdb_id])} in -> {len(sec_out_refs[sdb_id])} out"
                    + (f"; exports: {', '.join(s_exports)}" if s_exports else "")
                )
                cluster_rows.append(
                    (
                        sdb_id,
                        cdb_id,
                        1,
                        stitle,
                        len(sdids),
                        sloc,
                        json.dumps(s_in),
                        json.dumps(s_out),
                        ssummary,
                    )
                )
                sec_summaries.append(
                    {
                        "id": sdb_id,
                        "title": stitle,
                        "decl_count": len(sdids),
                        "total_loc": sloc,
                        "interface_in_count": len(sec_in_refs[sdb_id]),
                        "interface_out_count": len(sec_out_refs[sdb_id]),
                    }
                )

            chapters_summary.append(
                {
                    "id": cdb_id,
                    "title": ctitle,
                    "decl_count": len(chap_dids),
                    "total_loc": chap_loc,
                    "section_count": len(sids),
                    "interface_in_count": len(chap_in_refs[cdb_id]),
                    "interface_out_count": len(chap_out_refs[cdb_id]),
                    "key_exports": key_exports,
                    "sections": sec_summaries,
                }
            )

        conn.executemany(
            "INSERT INTO clusters "
            "(id, parent_id, level, title, decl_count, total_loc, interface_in_json, interface_out_json, summary) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            cluster_rows,
        )

        # Update metrics.cluster_id -> section id (level=1)
        upsert_sql = (
            "INSERT INTO metrics (decl_id, reachable, cluster_id) VALUES (?, 1, ?) "
            "ON CONFLICT(decl_id) DO UPDATE SET cluster_id = excluded.cluster_id"
        )
        batch: list[tuple[int, int]] = []
        for did, sdb_id in decl_final_sec_db.items():
            batch.append((did, sdb_id))
            if len(batch) >= batch_size:
                conn.executemany(upsert_sql, batch)
                batch.clear()
        if batch:
            conn.executemany(upsert_sql, batch)
            batch.clear()

        total_edges = internal_chap_edges + cross_chap_edges
        internal_ratio = (
            round(internal_chap_edges / total_edges, 4) if total_edges > 0 else 1.0
        )

        report = ClusterReport(
            total_declarations=len(proj_decls),
            total_loc=sum(d["body_loc"] for d in proj_decls.values()),
            chapter_count=len(ordered_cids),
            section_count=num_sections,
            total_cross_chapter_edges=cross_chap_edges,
            total_internal_chapter_edges=internal_chap_edges,
            internal_edge_ratio=internal_ratio,
            chapters=chapters_summary,
        )

        set_meta(conn, "analysis_cluster_stats", json.dumps(report.to_dict()))
        conn.commit()
        return report
    finally:
        if should_close:
            conn.close()
