"""Exact reverse-dependency reachability pruning and compression statistics."""

from __future__ import annotations

import json
import sqlite3
from collections import Counter, defaultdict, deque
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterable, Sequence

from proof_compressor.schema import connect_db, set_meta

_PREFERRED_ROOT_STEMS = (
    "main",
    "statements",
    "statement",
    "rh",
    "grh",
    "riemannhypothesis",
    "riemann_hypothesis",
)

_CANONICAL_ROOT_NAMES = (
    "rh",
    "grh",
    "riemann_hypothesis",
    "riemannhypothesis",
    "generalized_riemann_hypothesis",
    "generalizedriemannhypothesis",
    "main_theorem",
    "maintheorem",
)

_THEOREM_KINDS = frozenset({"theorem", "lemma"})


@dataclass
class PruneStats:
    """Exact dead-module and dead-declaration compression statistics."""

    root_ids: list[int] = field(default_factory=list)
    root_names: list[str] = field(default_factory=list)
    fallback_used: bool = False

    raw_modules: int = 0
    reachable_modules: int = 0
    dead_modules: int = 0
    module_elimination_pct: float = 0.0

    raw_project_loc: int = 0
    reachable_project_loc: int = 0
    dead_project_loc: int = 0
    loc_elimination_pct: float = 0.0

    raw_project_declarations: int = 0
    reachable_project_declarations: int = 0
    dead_project_declarations: int = 0
    declaration_elimination_pct: float = 0.0

    raw_project_decl_loc: int = 0
    reachable_project_decl_loc: int = 0
    dead_project_decl_loc: int = 0
    decl_loc_elimination_pct: float = 0.0

    total_mathlib_modules: int = 0
    mathlib_boundary_modules: int = 0
    total_mathlib_declarations: int = 0
    mathlib_boundary_declarations: int = 0

    import_reachable_modules: int = 0
    import_reachable_project_loc: int = 0

    top_dead_packages: list[dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _open_db(db: sqlite3.Connection | str | Path) -> tuple[sqlite3.Connection, bool]:
    if isinstance(db, sqlite3.Connection):
        return db, False
    return connect_db(db), True


def _pct(eliminated: int, total: int) -> float:
    if total <= 0:
        return 0.0
    return round(100.0 * eliminated / total, 2)


def _module_stem_lower(path: str) -> str:
    """Return lowercase leaf module/file stem for both slash-paths and dotted Lean module paths."""
    if not path:
        return ""
    norm = path.strip().replace("\\", "/")
    if norm.endswith(".lean"):
        norm = norm[:-5]
    if "/" in norm:
        norm = norm.rsplit("/", 1)[-1]
    elif "." in norm:
        norm = norm.rsplit(".", 1)[-1]
    return norm.lower()


def _is_top_level_module(path: str) -> bool:
    norm = (path or "").strip().replace("\\", "/")
    for prefix in ("./", "lean/src/", "src/"):
        if norm.startswith(prefix):
            norm = norm[len(prefix) :]
    if norm.endswith(".lean"):
        norm = norm[:-5]
    return "/" not in norm and "." not in norm


def _table_exists(conn: sqlite3.Connection, name: str) -> bool:
    row = conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = ?",
        (name,),
    ).fetchone()
    return row is not None


def _normalize_module_key(path: str) -> str:
    s = path.strip().replace("\\", "/")
    if s.startswith("./"):
        s = s[2:]
    if s.endswith(".lean"):
        s = s[:-5]
    return s.replace("/", ".")


def resolve_roots(
    conn: sqlite3.Connection,
    roots: Sequence[str] | None = None,
) -> list[tuple[int, str]]:
    """Resolve root theorem names (or auto-detect them) to (decl_id, full_name) pairs."""
    cur = conn.cursor()
    mod_paths: dict[int, tuple[str, int]] = {}
    for mid, path, is_mathlib in cur.execute(
        "SELECT id, path, is_mathlib FROM modules"
    ):
        mod_paths[mid] = (path or "", int(is_mathlib or 0))

    # Build lightweight lookup structures
    by_name: dict[str, tuple[int, str, str, int, int, str, int]] = {}
    by_short: dict[str, list[tuple[int, str, str, int, int, str, int]]] = defaultdict(list)
    by_name_lower: dict[str, list[tuple[int, str, str, int, int, str, int]]] = defaultdict(list)
    by_short_lower: dict[str, list[tuple[int, str, str, int, int, str, int]]] = defaultdict(list)
    by_mod: dict[int, list[tuple[int, str, str, int, int, str, int]]] = defaultdict(list)

    all_non_mathlib: list[tuple[int, str, str, int, int, str, int]] = []
    for did, name, short_name, mid, kind, is_mathlib, is_bk in cur.execute(
        "SELECT id, name, short_name, module_id, kind, is_mathlib, is_bookkeeping "
        "FROM declarations"
    ):
        rec = (
            int(did),
            name or "",
            short_name or "",
            int(mid or 0),
            int(is_mathlib or 0),
            (kind or "").lower(),
            int(is_bk or 0),
        )
        by_name[rec[1]] = rec
        if rec[2]:
            by_short[rec[2]].append(rec)
            by_short_lower[rec[2].lower()].append(rec)
        by_name_lower[rec[1].lower()].append(rec)
        by_mod[rec[3]].append(rec)
        if rec[4] == 0:
            all_non_mathlib.append(rec)

    def _rank_candidate(rec: tuple[int, str, str, int, int, str, int]) -> tuple[int, int, int, int, int, str]:
        _did, name, _short, mid, is_mathlib, kind, is_bk = rec
        mpath = mod_paths.get(mid, ("", 0))[0]
        stem = _module_stem_lower(mpath)
        pref_mod = 0 if stem in _PREFERRED_ROOT_STEMS else 1
        top_mod = 0 if _is_top_level_module(mpath) else 1
        is_thm = 0 if kind in _THEOREM_KINDS else 1
        return (is_mathlib, is_thm, pref_mod, top_mod, is_bk, name)

    resolved: list[tuple[int, str]] = []
    seen_ids: set[int] = set()

    def _add(rec: tuple[int, str, str, int, int, str, int]) -> None:
        if rec[0] not in seen_ids:
            seen_ids.add(rec[0])
            resolved.append((rec[0], rec[1]))

    if roots:
        clean_roots = [r.strip() for r in roots if r and r.strip()]
        for spec in clean_roots:
            # 1. Exact full name
            if spec in by_name:
                _add(by_name[spec])
                continue

            # 2. Exact short name
            if spec in by_short:
                cands = sorted(by_short[spec], key=_rank_candidate)
                # Keep best match (or all non-mathlib theorems in preferred root files)
                best = cands[0]
                _add(best)
                continue

            # 3. Dot-suffix match on full name
            suffix = "." + spec
            suffix_matches = [
                rec for name, rec in by_name.items() if name.endswith(suffix)
            ]
            if suffix_matches:
                suffix_matches.sort(key=_rank_candidate)
                _add(suffix_matches[0])
                continue

            # 4. Module path match (e.g. Main.lean, Main, or foo/Statements.lean)
            if spec.endswith(".lean") or "/" in spec or spec in {
                p for p, ml in mod_paths.values() if ml == 0
            }:
                spec_norm = spec.replace("\\", "/").lower()
                spec_key = _normalize_module_key(spec).lower()
                spec_stem = _module_stem_lower(spec)
                matched_mids = [
                    mid
                    for mid, (mpath, is_ml) in mod_paths.items()
                    if is_ml == 0
                    and (
                        mpath.replace("\\", "/").lower() == spec_norm
                        or mpath.replace("\\", "/").lower().endswith("/" + spec_norm)
                        or _normalize_module_key(mpath).lower() == spec_key
                        or (_is_top_level_module(mpath) and _module_stem_lower(mpath) == spec_stem)
                    )
                ]
                mod_decls: list[tuple[int, str, str, int, int, str, int]] = []
                for mid in matched_mids:
                    mod_decls.extend(by_mod.get(mid, []))
                thms = [r for r in mod_decls if r[4] == 0 and r[5] in _THEOREM_KINDS]
                picks = thms or [r for r in mod_decls if r[4] == 0 and r[6] == 0] or mod_decls
                for r in sorted(picks, key=_rank_candidate):
                    _add(r)
                if picks:
                    continue

            # 5. Case-insensitive name/short_name fallback
            low = spec.lower()
            ci_matches = by_name_lower.get(low) or by_short_lower.get(low)
            if ci_matches:
                ci_matches = sorted(ci_matches, key=_rank_candidate)
                _add(ci_matches[0])
                continue

        if not resolved:
            raise ValueError(f"No matching root declarations found for: {list(clean_roots)}")
        return resolved

    # Auto-detect roots when none specified
    # Priority 1: Non-Mathlib theorems in Main / Statements / RH / GRH modules
    # Prefer top-level Main/Statements before nested *.Main
    for top_only in (True, False):
        for target_stem in _PREFERRED_ROOT_STEMS:
            file_mids = [
                mid
                for mid, (mpath, is_ml) in mod_paths.items()
                if is_ml == 0
                and _module_stem_lower(mpath) == target_stem
                and (not top_only or _is_top_level_module(mpath))
            ]
            if not file_mids:
                continue
            file_decls: list[tuple[int, str, str, int, int, str, int]] = []
            for mid in file_mids:
                file_decls.extend(by_mod.get(mid, []))
            thms = [r for r in file_decls if r[4] == 0 and r[5] in _THEOREM_KINDS and r[6] == 0]
            if not thms:
                thms = [r for r in file_decls if r[4] == 0 and r[5] in _THEOREM_KINDS]
            if not thms:
                thms = [r for r in file_decls if r[4] == 0 and r[6] == 0]
            for r in sorted(thms, key=_rank_candidate):
                _add(r)
            if resolved:
                return resolved

    # Priority 2: Canonical theorem names (RH, GRH, riemann_hypothesis, ...)
    for cname in _CANONICAL_ROOT_NAMES:
        cands = [
            r
            for r in (by_short_lower.get(cname, []) + by_name_lower.get(cname, []))
            if r[4] == 0 and r[5] in _THEOREM_KINDS
        ]
        if cands:
            cands.sort(key=_rank_candidate)
            _add(cands[0])
    if resolved:
        return resolved

    # Priority 3: Top-level non-Mathlib theorems with in_degree == 0 from project decls
    if not all_non_mathlib:
        return []

    non_ml_ids = {r[0] for r in all_non_mathlib}
    in_deg_proj: Counter[int] = Counter()
    out_deg_proj: Counter[int] = Counter()
    for src_id, dst_id in cur.execute("SELECT DISTINCT src_id, dst_id FROM edges"):
        if src_id != dst_id and src_id in non_ml_ids:
            out_deg_proj[src_id] += 1
            if dst_id in non_ml_ids:
                in_deg_proj[dst_id] += 1

    zero_in_thms = [
        r
        for r in all_non_mathlib
        if r[5] in _THEOREM_KINDS and r[6] == 0 and in_deg_proj[r[0]] == 0
    ]
    if not zero_in_thms:
        zero_in_thms = [
            r for r in all_non_mathlib if r[5] in _THEOREM_KINDS and in_deg_proj[r[0]] == 0
        ]
    if not zero_in_thms:
        zero_in_thms = [r for r in all_non_mathlib if in_deg_proj[r[0]] == 0]
    if not zero_in_thms:
        zero_in_thms = all_non_mathlib

    # Prefer sinks that actually depend on other declarations
    with_deps = [r for r in zero_in_thms if out_deg_proj[r[0]] > 0]
    pool = with_deps or zero_in_thms
    pool.sort(key=lambda r: (-out_deg_proj[r[0]], r[1]))
    for r in pool[:20]:
        _add(r)
    return resolved


def prune_reachability(
    db: sqlite3.Connection | str | Path,
    roots: Sequence[str] | None = None,
    *,
    use_module_import_fallback: bool = True,
    batch_size: int = 50_000,
) -> PruneStats:
    """Run exact reverse-dependency reachability from root theorems and update `metrics`.

    Edge direction in SQLite: `(src_id, dst_id)` means `src_id` depends on `dst_id`.
    Traversal starts at `roots` and walks `src_id -> dst_id`, stopping at Mathlib
    declarations (recording direct Mathlib references as the Mathlib boundary without
    expanding Mathlib internals).
    """
    conn, should_close = _open_db(db)
    try:
        cur = conn.cursor()

        # Load modules metadata
        mod_path: dict[int, str] = {}
        mod_pkg: dict[int, str] = {}
        mod_loc: dict[int, int] = {}
        mod_is_ml: dict[int, int] = {}
        mod_key_to_id: dict[str, int] = {}

        for mid, path, pkg, loc, is_ml in cur.execute(
            "SELECT id, path, package, loc, is_mathlib FROM modules"
        ):
            mid = int(mid)
            p = path or ""
            mod_path[mid] = p
            mod_pkg[mid] = pkg or (p.split("/", 1)[0] if "/" in p else "root")
            mod_loc[mid] = int(loc or 0)
            mod_is_ml[mid] = int(is_ml or 0)
            if p:
                mod_key_to_id[_normalize_module_key(p)] = mid
                mod_key_to_id[p] = mid

        # Load declarations metadata
        decl_mod: dict[int, int] = {}
        decl_is_ml: dict[int, int] = {}
        decl_body_loc: dict[int, int] = {}
        mod_to_project_decls: dict[int, list[int]] = defaultdict(list)

        for did, mid, body_loc, is_ml in cur.execute(
            "SELECT id, module_id, body_loc, is_mathlib FROM declarations"
        ):
            did = int(did)
            mid_i = int(mid or 0)
            ml_i = int(is_ml or 0)
            decl_mod[did] = mid_i
            decl_is_ml[did] = ml_i
            decl_body_loc[did] = int(body_loc or 0)
            if ml_i == 0:
                mod_to_project_decls[mid_i].append(did)

        if not decl_mod:
            stats = PruneStats()
            set_meta(conn, "analysis_roots", json.dumps([]))
            set_meta(conn, "analysis_prune_stats", json.dumps(stats.to_dict()))
            conn.commit()
            return stats

        resolved_roots = resolve_roots(conn, roots)
        root_ids = [r[0] for r in resolved_roots]
        root_names = [r[1] for r in resolved_roots]

        # Build deduplicated adjacency list & global unique degrees (O(1) dedup via PK order)
        out_adj: dict[int, list[int]] = defaultdict(list)
        in_deg: Counter[int] = Counter()
        out_deg: Counter[int] = Counter()
        has_non_import_edge: set[int] = set()

        prev_src = -1
        prev_dst = -1
        for src_id, dst_id, kind in cur.execute(
            "SELECT src_id, dst_id, kind FROM edges ORDER BY src_id, dst_id"
        ):
            if src_id == dst_id:
                continue
            if kind != "import":
                has_non_import_edge.add(src_id)
            if src_id == prev_src and dst_id == prev_dst:
                continue
            prev_src = src_id
            prev_dst = dst_id
            out_adj[src_id].append(dst_id)
            out_deg[src_id] += 1
            in_deg[dst_id] += 1

        # Exact declaration-level BFS from roots along src_id -> dst_id
        reachable_project: set[int] = set()
        mathlib_boundary: set[int] = set()
        queue: deque[int] = deque()

        for rid in root_ids:
            if decl_is_ml.get(rid, 0) == 1:
                mathlib_boundary.add(rid)
            else:
                if rid not in reachable_project:
                    reachable_project.add(rid)
                    queue.append(rid)

        while queue:
            u = queue.popleft()
            for v in out_adj.get(u, ()):
                if v not in decl_is_ml:
                    continue
                if decl_is_ml[v] == 1:
                    mathlib_boundary.add(v)
                    continue
                if v not in reachable_project:
                    reachable_project.add(v)
                    queue.append(v)

        # Module-import reachability (used for reporting and fallback)
        import_reachable_mods: set[int] = set()
        import_mathlib_boundary_mods: set[int] = set()
        root_mod_ids = {
            decl_mod[rid]
            for rid in root_ids
            if rid in decl_mod and decl_mod[rid] in mod_is_ml
        }

        if _table_exists(conn, "module_imports") and root_mod_ids:
            mod_adj: dict[int, list[int]] = defaultdict(list)
            for src_mid, dst_path, dst_mid in cur.execute(
                "SELECT src_module_id, dst_module_path, dst_module_id FROM module_imports"
            ):
                target_mid = dst_mid
                if target_mid is None and dst_path:
                    target_mid = mod_key_to_id.get(dst_path) or mod_key_to_id.get(
                        _normalize_module_key(dst_path)
                    )
                if target_mid is not None and target_mid in mod_is_ml:
                    mod_adj[int(src_mid)].append(int(target_mid))

            mqueue: deque[int] = deque()
            for rmid in root_mod_ids:
                if mod_is_ml.get(rmid, 0) == 1:
                    import_mathlib_boundary_mods.add(rmid)
                elif rmid not in import_reachable_mods:
                    import_reachable_mods.add(rmid)
                    mqueue.append(rmid)

            while mqueue:
                m = mqueue.popleft()
                for nb in mod_adj.get(m, ()):
                    if mod_is_ml.get(nb, 0) == 1:
                        import_mathlib_boundary_mods.add(nb)
                    elif nb not in import_reachable_mods:
                        import_reachable_mods.add(nb)
                        mqueue.append(nb)

        # Activate module-import fallback only when roots had no declaration-level edges
        fallback_used = False
        roots_have_decl_edges = any(rid in has_non_import_edge for rid in root_ids)
        if (
            use_module_import_fallback
            and not roots_have_decl_edges
            and len(reachable_project) <= len(root_ids)
            and len(import_reachable_mods) > len(root_mod_ids)
        ):
            fallback_used = True
            for mid in import_reachable_mods:
                for did in mod_to_project_decls.get(mid, ()):
                    reachable_project.add(did)
                    for v in out_adj.get(did, ()):
                        if decl_is_ml.get(v, 0) == 1:
                            mathlib_boundary.add(v)

        reachable_all = reachable_project | mathlib_boundary

        # Persist metrics rows (reset stale reachability via upsert for every declaration)
        conn.execute("UPDATE metrics SET reachable = 0")
        upsert_sql = (
            "INSERT INTO metrics (decl_id, reachable, in_degree, out_degree) "
            "VALUES (?, ?, ?, ?) "
            "ON CONFLICT(decl_id) DO UPDATE SET "
            "reachable = excluded.reachable, "
            "in_degree = excluded.in_degree, "
            "out_degree = excluded.out_degree"
        )
        batch: list[tuple[int, int, int, int]] = []
        for did in decl_mod:
            batch.append(
                (
                    did,
                    1 if did in reachable_all else 0,
                    in_deg.get(did, 0),
                    out_deg.get(did, 0),
                )
            )
            if len(batch) >= batch_size:
                conn.executemany(upsert_sql, batch)
                batch.clear()
        if batch:
            conn.executemany(upsert_sql, batch)
            batch.clear()

        # Compute exact module & declaration compression statistics
        project_mod_ids = {mid for mid, is_ml in mod_is_ml.items() if is_ml == 0}
        mathlib_mod_ids = {mid for mid, is_ml in mod_is_ml.items() if is_ml == 1}

        reachable_mod_ids: set[int] = set()
        for did in reachable_project:
            mid = decl_mod.get(did)
            if mid in project_mod_ids:
                reachable_mod_ids.add(mid)
        for rmid in root_mod_ids:
            if rmid in project_mod_ids:
                reachable_mod_ids.add(rmid)

        mathlib_boundary_mod_ids: set[int] = set(import_mathlib_boundary_mods)
        for did in mathlib_boundary:
            mid = decl_mod.get(did)
            if mid in mathlib_mod_ids:
                mathlib_boundary_mod_ids.add(mid)

        # Also count direct module_imports from reachable project modules to mathlib modules
        if _table_exists(conn, "module_imports") and reachable_mod_ids:
            for src_mid, dst_path, dst_mid in cur.execute(
                "SELECT src_module_id, dst_module_path, dst_module_id FROM module_imports"
            ):
                if src_mid not in reachable_mod_ids:
                    continue
                target_mid = dst_mid
                if target_mid is None and dst_path:
                    target_mid = mod_key_to_id.get(dst_path) or mod_key_to_id.get(
                        _normalize_module_key(dst_path)
                    )
                if target_mid in mathlib_mod_ids:
                    mathlib_boundary_mod_ids.add(target_mid)

        raw_modules = len(project_mod_ids)
        reachable_modules = len(reachable_mod_ids)
        dead_modules = raw_modules - reachable_modules

        raw_project_loc = sum(mod_loc[m] for m in project_mod_ids)
        reachable_project_loc = sum(mod_loc[m] for m in reachable_mod_ids)
        dead_project_loc = raw_project_loc - reachable_project_loc

        raw_proj_decls = sum(1 for is_ml in decl_is_ml.values() if is_ml == 0)
        reach_proj_decls = len(reachable_project)
        dead_proj_decls = raw_proj_decls - reach_proj_decls

        raw_proj_decl_loc = sum(
            decl_body_loc[d] for d, is_ml in decl_is_ml.items() if is_ml == 0
        )
        reach_proj_decl_loc = sum(decl_body_loc[d] for d in reachable_project)
        dead_proj_decl_loc = raw_proj_decl_loc - reach_proj_decl_loc

        total_ml_decls = sum(1 for is_ml in decl_is_ml.values() if is_ml == 1)
        import_reach_loc = sum(mod_loc[m] for m in import_reachable_mods if m in project_mod_ids)

        # Dead code breakdown by package
        dead_pkg_loc: Counter[str] = Counter()
        dead_pkg_mods: Counter[str] = Counter()
        for mid in project_mod_ids - reachable_mod_ids:
            pkg = mod_pkg.get(mid, "unknown")
            dead_pkg_loc[pkg] += mod_loc[mid]
            dead_pkg_mods[pkg] += 1

        top_dead_packages = [
            {
                "package": pkg,
                "dead_modules": dead_pkg_mods[pkg],
                "dead_loc": loc,
            }
            for pkg, loc in dead_pkg_loc.most_common(15)
        ]

        stats = PruneStats(
            root_ids=root_ids,
            root_names=root_names,
            fallback_used=fallback_used,
            raw_modules=raw_modules,
            reachable_modules=reachable_modules,
            dead_modules=dead_modules,
            module_elimination_pct=_pct(dead_modules, raw_modules),
            raw_project_loc=raw_project_loc,
            reachable_project_loc=reachable_project_loc,
            dead_project_loc=dead_project_loc,
            loc_elimination_pct=_pct(dead_project_loc, raw_project_loc),
            raw_project_declarations=raw_proj_decls,
            reachable_project_declarations=reach_proj_decls,
            dead_project_declarations=dead_proj_decls,
            declaration_elimination_pct=_pct(dead_proj_decls, raw_proj_decls),
            raw_project_decl_loc=raw_proj_decl_loc,
            reachable_project_decl_loc=reach_proj_decl_loc,
            dead_project_decl_loc=dead_proj_decl_loc,
            decl_loc_elimination_pct=_pct(dead_proj_decl_loc, raw_proj_decl_loc),
            total_mathlib_modules=len(mathlib_mod_ids),
            mathlib_boundary_modules=len(mathlib_boundary_mod_ids),
            total_mathlib_declarations=total_ml_decls,
            mathlib_boundary_declarations=len(mathlib_boundary),
            import_reachable_modules=len(import_reachable_mods),
            import_reachable_project_loc=import_reach_loc,
            top_dead_packages=top_dead_packages,
        )

        set_meta(
            conn,
            "analysis_roots",
            json.dumps([{"id": rid, "name": rname} for rid, rname in resolved_roots]),
        )
        set_meta(conn, "analysis_prune_stats", json.dumps(stats.to_dict()))
        conn.commit()
        return stats
    finally:
        if should_close:
            conn.close()
