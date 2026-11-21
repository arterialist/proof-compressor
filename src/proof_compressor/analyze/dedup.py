"""Canonical deduplication, signature similarity, and Mathlib-absorption analysis."""

from __future__ import annotations

import hashlib
import json
import re
import sqlite3
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from proof_compressor.schema import connect_db, set_meta

_COMMENT_LINE_RE = re.compile(r"--[^\n]*")
_COMMENT_BLOCK_RE = re.compile(r"/-.*?-/", re.DOTALL)
_UNIVERSE_RE = re.compile(r"\.\{[^}]*\}")
_BINDER_RE = re.compile(r"[\(\{\[]\s*([A-Za-z_][A-Za-z0-9_' ]*?)\s*:\s*([^)\}\]]+)[\)\}\]]")
_IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_'.]*\b")
_WS_RE = re.compile(r"\s+")

_LEAN_KEYWORDS = frozenset(
    {
        "forall",
        "fun",
        "let",
        "in",
        "if",
        "then",
        "else",
        "match",
        "with",
        "where",
        "by",
        "Type",
        "Prop",
        "Sort",
        "True",
        "False",
        "And",
        "Or",
        "Not",
        "Exists",
    }
)

_MATHLIB_NAME_PATTERNS = re.compile(
    r"(?:^|_)(?:aux|helper|compat|polyfill|mathlib|missing|std|le_of|lt_of|eq_of|ne_of|"
    r"nonneg|nonpos|pos_of|neg_of|add_comm|mul_comm|add_assoc|mul_assoc|"
    r"mem_|card_|sum_|prod_|finset_|set_|measurable_|continuous_|integrable_|"
    r"differentiable_|tendsto_|norm_|abs_|cast_|coe_|ofNat|toReal|toComplex)",
    re.IGNORECASE,
)

_MATHLIB_SIG_TOKENS = frozenset(
    {
        "Real",
        "Complex",
        "Nat",
        "Int",
        "Rat",
        "ENNReal",
        "NNReal",
        "Finset",
        "Fintype",
        "Set",
        "List",
        "Array",
        "Multiset",
        "Filter",
        "Tendsto",
        "MeasureTheory",
        "Measure",
        "Integrable",
        "Measurable",
        "Continuous",
        "Differentiable",
        "Polynomial",
        "Matrix",
        "LinearMap",
        "Submodule",
        "AddCommGroup",
        "CommRing",
        "Field",
        "NormedSpace",
        "MetricSpace",
        "TopologicalSpace",
        "CompleteSpace",
        "Order",
        "LinearOrder",
        "ℝ",
        "ℂ",
        "ℕ",
        "ℤ",
        "ℚ",
    }
)

_DEF_KINDS = frozenset({"def", "abbrev", "structure", "class", "inductive"})
_THM_KINDS = frozenset({"theorem", "lemma"})


@dataclass
class DedupReport:
    """Structured deduplication and Mathlib-absorption analysis report."""

    analyzed_declarations: int = 0
    analyzed_loc: int = 0

    exact_duplicate_group_count: int = 0
    exact_duplicate_redundant_decls: int = 0
    exact_duplicate_reducible_loc: int = 0

    near_duplicate_group_count: int = 0
    near_duplicate_redundant_decls: int = 0
    near_duplicate_reducible_loc: int = 0

    isomorphic_def_group_count: int = 0
    isomorphic_def_redundant_decls: int = 0

    mathlib_absorption_candidates: int = 0
    mathlib_absorption_loc: int = 0

    total_estimated_reducible_decls: int = 0
    total_estimated_reducible_loc: int = 0
    estimated_post_dedup_loc: int = 0
    dedup_reduction_pct: float = 0.0

    top_exact_duplicate_groups: list[dict[str, Any]] = field(default_factory=list)
    top_near_duplicate_groups: list[dict[str, Any]] = field(default_factory=list)
    top_isomorphic_defs: list[dict[str, Any]] = field(default_factory=list)
    top_mathlib_candidates: list[dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _open_db(db: sqlite3.Connection | str | Path) -> tuple[sqlite3.Connection, bool]:
    if isinstance(db, sqlite3.Connection):
        return db, False
    return connect_db(db), True


def normalize_signature(type_sig: str | None) -> str:
    """Deeply normalize a Lean type signature modulo binder names, namespaces, and whitespace."""
    if not type_sig:
        return ""
    s = _COMMENT_BLOCK_RE.sub(" ", type_sig)
    s = _COMMENT_LINE_RE.sub(" ", s)
    s = _UNIVERSE_RE.sub("", s)
    s = s.replace("∀", "forall ").replace("→", " -> ").replace("↔", " <-> ")
    s = _WS_RE.sub(" ", s).strip()

    # Collect alpha-bound variable names from binders and canonicalize them
    binder_map: dict[str, str] = {}
    counter = 0

    def _replace_binder(match: re.Match[str]) -> str:
        nonlocal counter
        raw_vars = match.group(1).strip().split()
        raw_ty = match.group(2).strip()
        canon_vars: list[str] = []
        for v in raw_vars:
            if v == "_" or v in _LEAN_KEYWORDS:
                canon_vars.append(v)
                continue
            if v not in binder_map:
                binder_map[v] = f"v{counter}"
                counter += 1
            canon_vars.append(binder_map[v])
        return f"({' '.join(canon_vars)} : {raw_ty})"

    s = _BINDER_RE.sub(_replace_binder, s)

    # Strip namespace qualifiers on identifiers and substitute bound variable names
    def _replace_ident(match: re.Match[str]) -> str:
        tok = match.group(0)
        if tok in binder_map:
            return binder_map[tok]
        if "." in tok:
            return tok.rsplit(".", 1)[-1]
        return tok

    s = _IDENT_RE.sub(_replace_ident, s)
    s = _WS_RE.sub(" ", s).strip()
    return s


def signature_tokens(norm_sig: str) -> frozenset[str]:
    """Extract normalized identifier/symbol tokens for fast similarity scoring."""
    if not norm_sig:
        return frozenset()
    raw = re.findall(r"[A-Za-z_][A-Za-z0-9_']*|[≤≥≠↔→∀∃∑∏∫ℝℂℕℤℚ+\-*/=<>]+", norm_sig)
    return frozenset(t for t in raw if t not in _LEAN_KEYWORDS and not re.fullmatch(r"v\d+", t))


def _deep_hash(norm_sig: str) -> str:
    return hashlib.sha1(norm_sig.encode("utf-8")).hexdigest()[:16]


def _jaccard(a: frozenset[str], b: frozenset[str]) -> float:
    if not a or not b:
        return 0.0
    inter = len(a & b)
    if inter == 0:
        return 0.0
    return inter / (len(a) + len(b) - inter)


def _kind_group(kind: str) -> str:
    k = (kind or "").lower()
    if k in _THM_KINDS:
        return "thm"
    if k in _DEF_KINDS:
        return "def"
    return k or "other"


def analyze_dedup(
    db: sqlite3.Connection | str | Path,
    *,
    reachable_only: bool = True,
    similarity_threshold: float = 0.85,
    max_bucket_scan: int = 64,
    top_groups: int = 30,
) -> DedupReport:
    """Identify exact duplicates, near-duplicate signatures, isomorphic defs, and Mathlib candidates."""
    conn, should_close = _open_db(db)
    try:
        cur = conn.cursor()

        # Check whether reachability metrics exist
        has_reachable = False
        if reachable_only:
            row = cur.execute(
                "SELECT 1 FROM metrics WHERE reachable = 1 LIMIT 1"
            ).fetchone()
            has_reachable = row is not None

        if reachable_only and has_reachable:
            query = (
                "SELECT d.id, d.name, d.short_name, d.module_id, d.kind, d.type_sig, "
                "d.canonical_type_hash, d.body_loc, d.docstring, d.is_bookkeeping, "
                "COALESCE(m.in_degree, 0) "
                "FROM declarations d "
                "JOIN metrics m ON m.decl_id = d.id "
                "WHERE m.reachable = 1 AND d.is_mathlib = 0"
            )
        else:
            query = (
                "SELECT d.id, d.name, d.short_name, d.module_id, d.kind, d.type_sig, "
                "d.canonical_type_hash, d.body_loc, d.docstring, d.is_bookkeeping, "
                "COALESCE(m.in_degree, 0) "
                "FROM declarations d "
                "LEFT JOIN metrics m ON m.decl_id = d.id "
                "WHERE d.is_mathlib = 0"
            )

        decls: dict[int, dict[str, Any]] = {}
        for (
            did,
            name,
            short_name,
            mid,
            kind,
            type_sig,
            chash,
            body_loc,
            docstring,
            is_bk,
            in_deg,
        ) in cur.execute(query):
            did_i = int(did)
            decls[did_i] = {
                "id": did_i,
                "name": name or "",
                "short_name": short_name or "",
                "module_id": int(mid or 0),
                "kind": (kind or "").lower(),
                "kind_group": _kind_group(kind or ""),
                "type_sig": type_sig or "",
                "canonical_type_hash": (chash or "").strip(),
                "body_loc": int(body_loc or 0),
                "has_doc": bool(docstring and docstring.strip()),
                "is_bookkeeping": int(is_bk or 0),
                "in_degree": int(in_deg or 0),
            }

        if not decls:
            report = DedupReport()
            set_meta(conn, "analysis_dedup_stats", json.dumps(report.to_dict()))
            set_meta(conn, "analysis_dedup_groups", json.dumps([]))
            conn.commit()
            return report

        # Collect Mathlib canonical_type_hashes for exact Mathlib match detection
        mathlib_hashes: dict[str, str] = {}
        for name, chash in cur.execute(
            "SELECT name, canonical_type_hash FROM declarations "
            "WHERE is_mathlib = 1 AND canonical_type_hash IS NOT NULL AND canonical_type_hash != ''"
        ):
            if chash not in mathlib_hashes:
                mathlib_hashes[chash] = name or ""

        def _rep_sort_key(d: dict[str, Any]) -> tuple[int, int, int, int, int, str]:
            return (
                d["is_bookkeeping"],
                0 if d["has_doc"] else 1,
                -d["in_degree"],
                len(d["name"]),
                d["body_loc"],
                d["name"],
            )

        # 1. Exact canonical_type_hash duplicate grouping
        by_chash: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
        for d in decls.values():
            ch = d["canonical_type_hash"]
            if ch:
                by_chash[(d["kind_group"], ch)].append(d)

        exact_redundant_ids: set[int] = set()
        exact_groups: list[dict[str, Any]] = []
        iso_def_groups: list[dict[str, Any]] = []
        iso_def_redundant_ids: set[int] = set()

        for (kg, ch), members in by_chash.items():
            if len(members) < 2:
                continue
            members.sort(key=_rep_sort_key)
            rep = members[0]
            dups = members[1:]
            reducible_loc = sum(x["body_loc"] for x in dups)
            for x in dups:
                exact_redundant_ids.add(x["id"])
                if kg == "def":
                    iso_def_redundant_ids.add(x["id"])

            group_rec = {
                "hash": ch,
                "kind_group": kg,
                "count": len(members),
                "reducible_loc": reducible_loc,
                "canonical": {
                    "id": rep["id"],
                    "name": rep["name"],
                    "body_loc": rep["body_loc"],
                },
                "duplicates": [
                    {"id": x["id"], "name": x["name"], "body_loc": x["body_loc"]}
                    for x in dups[:10]
                ],
                "type_sig_preview": rep["type_sig"][:200],
            }
            exact_groups.append(group_rec)
            if kg == "def":
                iso_def_groups.append(group_rec)

        exact_groups.sort(key=lambda g: (-g["reducible_loc"], -g["count"]))

        # 2. Deep normalized signature & near-duplicate detection
        # Precompute normalized signatures only for non-empty type_sigs
        norm_by_deep: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
        token_cache: dict[int, frozenset[str]] = {}
        buckets: dict[tuple[str, str, int], list[int]] = defaultdict(list)

        for did, d in decls.items():
            if did in exact_redundant_ids:
                continue
            sig = d["type_sig"]
            if not sig or len(sig) < 8:
                continue
            nsig = normalize_signature(sig)
            if not nsig:
                continue
            dhash = _deep_hash(nsig)
            norm_by_deep[(d["kind_group"], dhash)].append(d)

            toks = signature_tokens(nsig)
            if len(toks) >= 3:
                token_cache[did] = toks
                # Coarse LSH-style bucket: (kind_group, longest/rarest-looking token, token count band)
                anchor = max(toks, key=lambda t: (len(t), t))
                band = len(toks) // 3
                buckets[(d["kind_group"], anchor, band)].append(did)

        near_redundant_ids: set[int] = set()
        near_groups: list[dict[str, Any]] = []

        # 2a. Exact deep-normalized matches (alpha/namespace/implicit-binder isomorphic)
        already_near_grouped: set[int] = set()
        for (kg, dhash), members in norm_by_deep.items():
            if len(members) < 2:
                continue
            # Ensure they weren't already identical canonical_type_hash
            distinct_chashes = {m["canonical_type_hash"] for m in members if m["canonical_type_hash"]}
            if len(distinct_chashes) <= 1 and all(m["canonical_type_hash"] for m in members):
                continue
            members.sort(key=_rep_sort_key)
            rep = members[0]
            dups = members[1:]
            reducible_loc = sum(x["body_loc"] for x in dups)
            for x in dups:
                near_redundant_ids.add(x["id"])
                already_near_grouped.add(x["id"])
                if kg == "def":
                    iso_def_redundant_ids.add(x["id"])
            already_near_grouped.add(rep["id"])
            rec = {
                "match_type": "alpha_namespace_isomorphic",
                "similarity": 1.0,
                "kind_group": kg,
                "count": len(members),
                "reducible_loc": reducible_loc,
                "canonical": {
                    "id": rep["id"],
                    "name": rep["name"],
                    "body_loc": rep["body_loc"],
                },
                "duplicates": [
                    {"id": x["id"], "name": x["name"], "body_loc": x["body_loc"]}
                    for x in dups[:10]
                ],
                "type_sig_preview": rep["type_sig"][:200],
            }
            near_groups.append(rec)
            if kg == "def":
                iso_def_groups.append(rec)

        # 2b. Bucketed Jaccard similarity for near-duplicates (bounded window for O(N) scaling)
        for (kg, _anchor, _band), id_list in buckets.items():
            if len(id_list) < 2:
                continue
            # Filter out declarations already grouped
            cands = [i for i in id_list if i not in already_near_grouped]
            if len(cands) < 2:
                continue
            # Sort by token count and short_name to place closest signatures adjacent
            cands.sort(key=lambda i: (len(token_cache[i]), decls[i]["short_name"]))
            window = min(len(cands), max_bucket_scan)
            local_visited: set[int] = set()
            for idx_a in range(len(cands)):
                a = cands[idx_a]
                if a in local_visited:
                    continue
                toks_a = token_cache[a]
                cluster = [decls[a]]
                end_b = min(len(cands), idx_a + window)
                min_sim = 1.0
                for idx_b in range(idx_a + 1, end_b):
                    b = cands[idx_b]
                    if b in local_visited:
                        continue
                    toks_b = token_cache[b]
                    # Quick length ratio bound for Jaccard
                    la, lb = len(toks_a), len(toks_b)
                    if min(la, lb) / max(la, lb) < similarity_threshold:
                        continue
                    sim = _jaccard(toks_a, toks_b)
                    if sim >= similarity_threshold:
                        cluster.append(decls[b])
                        local_visited.add(b)
                        if sim < min_sim:
                            min_sim = sim
                if len(cluster) >= 2:
                    local_visited.add(a)
                    cluster.sort(key=_rep_sort_key)
                    rep = cluster[0]
                    dups = cluster[1:]
                    reducible_loc = sum(x["body_loc"] for x in dups)
                    for x in dups:
                        near_redundant_ids.add(x["id"])
                        already_near_grouped.add(x["id"])
                        if kg == "def":
                            iso_def_redundant_ids.add(x["id"])
                    already_near_grouped.add(rep["id"])
                    rec = {
                        "match_type": "token_jaccard",
                        "similarity": round(min_sim, 3),
                        "kind_group": kg,
                        "count": len(cluster),
                        "reducible_loc": reducible_loc,
                        "canonical": {
                            "id": rep["id"],
                            "name": rep["name"],
                            "body_loc": rep["body_loc"],
                        },
                        "duplicates": [
                            {"id": x["id"], "name": x["name"], "body_loc": x["body_loc"]}
                            for x in dups[:10]
                        ],
                        "type_sig_preview": rep["type_sig"][:200],
                    }
                    near_groups.append(rec)
                    if kg == "def":
                        iso_def_groups.append(rec)

        near_groups.sort(key=lambda g: (-g["reducible_loc"], -g["count"]))
        iso_def_groups.sort(key=lambda g: (-g["reducible_loc"], -g["count"]))

        # 3. Mathlib-absorption candidates
        # Count distinct modules per short_name to spot repeated helper lemmas
        short_name_mods: dict[str, set[int]] = defaultdict(set)
        for d in decls.values():
            sn = d["short_name"]
            if sn and len(sn) >= 3:
                short_name_mods[sn].add(d["module_id"])

        mathlib_candidates: list[dict[str, Any]] = []
        mathlib_cand_ids: set[int] = set()

        for did, d in decls.items():
            reasons: list[str] = []
            ch = d["canonical_type_hash"]
            if ch and ch in mathlib_hashes:
                reasons.append(f"exact_mathlib_type_match:{mathlib_hashes[ch]}")

            sn = d["short_name"]
            sig = d["type_sig"]
            toks = token_cache.get(did)
            if toks is None and sig:
                toks = signature_tokens(normalize_signature(sig))

            name_matches = bool(_MATHLIB_NAME_PATTERNS.search(sn))
            std_hits = len(toks & _MATHLIB_SIG_TOKENS) if toks else 0
            std_ratio = (std_hits / len(toks)) if toks else 0.0

            if name_matches and (std_hits >= 1 or d["is_bookkeeping"] == 1):
                reasons.append("mathlib_api_pattern")
            elif std_hits >= 2 and std_ratio >= 0.45 and d["body_loc"] <= 40:
                reasons.append("standard_library_signature")

            if sn and len(short_name_mods.get(sn, ())) >= 3 and (
                name_matches or d["is_bookkeeping"] == 1 or d["body_loc"] <= 25
            ):
                reasons.append(f"repeated_helper_across_{len(short_name_mods[sn])}_modules")

            if reasons:
                mathlib_cand_ids.add(did)
                mathlib_candidates.append(
                    {
                        "id": did,
                        "name": d["name"],
                        "kind": d["kind"],
                        "body_loc": d["body_loc"],
                        "in_degree": d["in_degree"],
                        "reasons": reasons,
                        "type_sig_preview": sig[:180],
                    }
                )

        mathlib_candidates.sort(key=lambda c: (-c["body_loc"], -c["in_degree"], c["name"]))

        # 4. Aggregate non-double-counted LOC reduction estimates
        analyzed_loc = sum(d["body_loc"] for d in decls.values())
        exact_loc = sum(decls[i]["body_loc"] for i in exact_redundant_ids)
        near_loc = sum(decls[i]["body_loc"] for i in near_redundant_ids)
        ml_loc = sum(decls[i]["body_loc"] for i in mathlib_cand_ids)

        union_reducible = exact_redundant_ids | near_redundant_ids | mathlib_cand_ids
        total_reducible_loc = sum(decls[i]["body_loc"] for i in union_reducible)
        post_dedup_loc = max(0, analyzed_loc - total_reducible_loc)
        reduction_pct = (
            round(100.0 * total_reducible_loc / analyzed_loc, 2)
            if analyzed_loc > 0
            else 0.0
        )

        report = DedupReport(
            analyzed_declarations=len(decls),
            analyzed_loc=analyzed_loc,
            exact_duplicate_group_count=len(exact_groups),
            exact_duplicate_redundant_decls=len(exact_redundant_ids),
            exact_duplicate_reducible_loc=exact_loc,
            near_duplicate_group_count=len(near_groups),
            near_duplicate_redundant_decls=len(near_redundant_ids),
            near_duplicate_reducible_loc=near_loc,
            isomorphic_def_group_count=len(iso_def_groups),
            isomorphic_def_redundant_decls=len(iso_def_redundant_ids),
            mathlib_absorption_candidates=len(mathlib_cand_ids),
            mathlib_absorption_loc=ml_loc,
            total_estimated_reducible_decls=len(union_reducible),
            total_estimated_reducible_loc=total_reducible_loc,
            estimated_post_dedup_loc=post_dedup_loc,
            dedup_reduction_pct=reduction_pct,
            top_exact_duplicate_groups=exact_groups[:top_groups],
            top_near_duplicate_groups=near_groups[:top_groups],
            top_isomorphic_defs=iso_def_groups[:top_groups],
            top_mathlib_candidates=mathlib_candidates[:top_groups],
        )

        set_meta(conn, "analysis_dedup_stats", json.dumps(report.to_dict()))
        set_meta(
            conn,
            "analysis_dedup_groups",
            json.dumps(
                {
                    "exact": exact_groups[:top_groups],
                    "near": near_groups[:top_groups],
                    "isomorphic_defs": iso_def_groups[:top_groups],
                    "mathlib_candidates": mathlib_candidates[:top_groups],
                }
            ),
        )
        conn.commit()
        return report
    finally:
        if should_close:
            conn.close()
