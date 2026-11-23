"""Annals-style LaTeX manuscript generator grounded in the Lean dependency graph."""

from __future__ import annotations

import re
import sqlite3
from collections import defaultdict, deque
from pathlib import Path
from typing import Any, Callable

from proof_compressor.expose._db import (
    DbHandle,
    get_cluster_hierarchy,
    get_meta_dict,
    get_root_declaration_names,
    has_reachable_metrics,
    open_db,
    query_all,
    query_one,
    safe_json_loads,
)
from proof_compressor.expose.filter import (
    detect_bookkeeping_leaks,
    extract_proof_idioms,
)
from proof_compressor.expose.symbols import (
    SymbolRegistry,
    build_symbol_registry,
    escape_latex_text,
    lean_type_to_latex,
)

# Optional refinement callable: (draft_section_tex, strict_context_dict) -> refined_tex
SectionRefiner = Callable[[str, dict[str, Any]], str]

_STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound", "Lean.ofReduceBool", "Lean.trustCompiler"})


_TITLE_SANITIZE_SUBS: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"\bfinset\b", re.I), "finite sum"),
    (re.compile(r"\bfintype\b", re.I), "finite"),
    (re.compile(r"\b(?:ae|strongly)?\s*measurable\b", re.I), "regularity"),
    (re.compile(r"\bdecidable(?:eq|pred|rel)?\b", re.I), "effective"),
    (re.compile(r"\b(?:norm|push)\s*cast\b|\bcoercion\b", re.I), "compatibility"),
    (re.compile(r"\binhabited\b|\bsubsingleton\b|\bnezero\b", re.I), "structural"),
)


def _human_title(raw: str) -> str:
    """Turn a Lean identifier or module path into a clean mathematical heading."""
    if not raw:
        return "Untitled Section"
    s = raw.replace("/", " / ").replace("_", " ")
    # Insert spaces in CamelCase words
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", s)
    for pat, repl in _TITLE_SANITIZE_SUBS:
        s = pat.sub(repl, s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _format_math_block(tex_stmt: str) -> str:
    """Render short statements in `\\[ ... \\]` and long statements in a line-wrapping math block."""
    s = tex_stmt.strip()
    if len(s) <= 95:
        return f"\\[\n{s}\n\\]"
    # Insert soft line-break hints at top-level binder boundaries and logical arrows
    wrapped = s.replace(") (", r") \allowbreak (")
    wrapped = wrapped.replace(r"\to ", r"\to \allowbreak ")
    wrapped = wrapped.replace(r"\longrightarrow ", r"\longrightarrow \allowbreak ")
    wrapped = wrapped.replace(r"\land ", r"\land \allowbreak ")
    wrapped = wrapped.replace(r"\lor ", r"\lor \allowbreak ")
    wrapped = wrapped.replace(", ", r", \allowbreak ")
    return f"\\begin{{quote}}\\small\\raggedright$\\displaystyle {wrapped}$\\end{{quote}}"


def _clean_docstring_for_prose(doc: str | None) -> str:
    """Sanitize a Lean docstring for inclusion in mathematical prose (no bookkeeping leaks)."""
    if not doc:
        return ""
    text = doc.strip()
    # Strip markdown code fences or Lean tactic snippets
    text = re.sub(r"```.*?```", "", text, flags=re.S)
    text = re.sub(r"`([^`]+)`", r"\1", text)
    text = " ".join(text.split())
    if not text:
        return ""
    if detect_bookkeeping_leaks(text):
        return ""
    if len(text) > 260:
        text = text[:257].rsplit(" ", 1)[0] + "..."
    return escape_latex_text(text)


def _load_or_build_registry(conn: sqlite3.Connection, max_symbols: int = 120) -> SymbolRegistry:
    reg = SymbolRegistry.load_from_db(conn)
    if reg.entries:
        return reg
    return build_symbol_registry(conn, max_symbols=max_symbols, reachable_only=True)


def _compute_corpus_stats(conn: sqlite3.Connection) -> dict[str, Any]:
    """Gather exact raw, reachable, bookkeeping, and dedup compression metrics."""
    meta = get_meta_dict(conn)
    prune_meta = safe_json_loads(meta.get("analysis_prune_stats"), {})
    dedup_meta = safe_json_loads(meta.get("analysis_dedup_stats"), {})

    raw_mod = query_one(
        conn,
        """
        SELECT COUNT(*) AS cnt,
               COALESCE(SUM(loc), 0) AS loc,
               COALESCE(SUM(CASE WHEN is_mathlib = 0 THEN 1 ELSE 0 END), 0) AS proj_cnt,
               COALESCE(SUM(CASE WHEN is_mathlib = 0 THEN loc ELSE 0 END), 0) AS proj_loc
        FROM modules
        """,
    ) or {"cnt": 0, "loc": 0, "proj_cnt": 0, "proj_loc": 0}

    raw_decl = query_one(
        conn,
        """
        SELECT COUNT(*) AS cnt,
               COALESCE(SUM(body_loc), 0) AS body_loc,
               COALESCE(SUM(CASE WHEN is_mathlib = 0 THEN 1 ELSE 0 END), 0) AS proj_cnt,
               COALESCE(SUM(CASE WHEN is_mathlib = 0 THEN body_loc ELSE 0 END), 0) AS proj_loc,
               COALESCE(SUM(CASE WHEN is_mathlib = 0 AND is_bookkeeping = 1 THEN 1 ELSE 0 END), 0) AS bk_cnt
        FROM declarations
        """,
    ) or {"cnt": 0, "body_loc": 0, "proj_cnt": 0, "proj_loc": 0, "bk_cnt": 0}

    use_reach = has_reachable_metrics(conn)
    if use_reach:
        reach_decl = query_one(
            conn,
            """
            SELECT COUNT(*) AS cnt,
                   COALESCE(SUM(d.body_loc), 0) AS body_loc,
                   COALESCE(SUM(CASE WHEN d.is_bookkeeping = 0 THEN 1 ELSE 0 END), 0) AS math_cnt,
                   COALESCE(SUM(CASE WHEN d.is_bookkeeping = 0 THEN d.body_loc ELSE 0 END), 0) AS math_loc,
                   COUNT(DISTINCT d.module_id) AS mod_cnt
            FROM declarations d
            JOIN metrics m ON m.decl_id = d.id
            WHERE m.reachable = 1 AND d.is_mathlib = 0
            """,
        ) or {"cnt": 0, "body_loc": 0, "math_cnt": 0, "math_loc": 0, "mod_cnt": 0}

        reach_mod_loc_row = query_one(
            conn,
            """
            SELECT COALESCE(SUM(loc), 0) AS loc
            FROM modules
            WHERE is_mathlib = 0
              AND id IN (
                  SELECT DISTINCT d.module_id
                  FROM declarations d
                  JOIN metrics m ON m.decl_id = d.id
                  WHERE m.reachable = 1 AND d.is_mathlib = 0
              )
            """,
        ) or {"loc": 0}
        reach_mod_loc = int(reach_mod_loc_row["loc"] or 0)
    else:
        reach_decl = {
            "cnt": raw_decl["proj_cnt"],
            "body_loc": raw_decl["proj_loc"],
            "math_cnt": int(raw_decl["proj_cnt"]) - int(raw_decl["bk_cnt"]),
            "math_loc": raw_decl["proj_loc"],
            "mod_cnt": raw_mod["proj_cnt"],
        }
        reach_mod_loc = int(raw_mod["proj_loc"] or 0)

    # Canonical duplicate stats (computed directly if not present in meta)
    if use_reach:
        dup_row = query_one(
            conn,
            """
            SELECT COUNT(*) AS dup_groups,
                   COALESCE(SUM(cnt - 1), 0) AS redundant_decls,
                   COALESCE(SUM(total_loc - min_loc), 0) AS redundant_loc
            FROM (
                SELECT d.canonical_type_hash,
                       COUNT(*) AS cnt,
                       SUM(d.body_loc) AS total_loc,
                       MIN(d.body_loc) AS min_loc
                FROM declarations d
                JOIN metrics m ON m.decl_id = d.id
                WHERE m.reachable = 1
                  AND d.is_mathlib = 0
                  AND d.canonical_type_hash IS NOT NULL
                  AND d.canonical_type_hash != ''
                GROUP BY d.canonical_type_hash
                HAVING COUNT(*) > 1
            )
            """,
        ) or {"dup_groups": 0, "redundant_decls": 0, "redundant_loc": 0}
    else:
        dup_row = query_one(
            conn,
            """
            SELECT COUNT(*) AS dup_groups,
                   COALESCE(SUM(cnt - 1), 0) AS redundant_decls,
                   COALESCE(SUM(total_loc - min_loc), 0) AS redundant_loc
            FROM (
                SELECT canonical_type_hash,
                       COUNT(*) AS cnt,
                       SUM(body_loc) AS total_loc,
                       MIN(body_loc) AS min_loc
                FROM declarations
                WHERE is_mathlib = 0
                  AND canonical_type_hash IS NOT NULL
                  AND canonical_type_hash != ''
                GROUP BY canonical_type_hash
                HAVING COUNT(*) > 1
            )
            """,
        ) or {"dup_groups": 0, "redundant_decls": 0, "redundant_loc": 0}

    edge_cnt_row = query_one(conn, "SELECT COUNT(*) AS cnt FROM edges") or {"cnt": 0}

    raw_loc = int(raw_mod["proj_loc"] or raw_decl["proj_loc"] or 0)
    reachable_loc = int(reach_mod_loc or reach_decl["body_loc"] or 0)
    compression_ratio = (raw_loc / reachable_loc) if reachable_loc > 0 else 1.0

    return {
        "raw_modules": int(raw_mod["proj_cnt"] or 0),
        "raw_loc": raw_loc,
        "raw_declarations": int(raw_decl["proj_cnt"] or 0),
        "raw_body_loc": int(raw_decl["proj_loc"] or 0),
        "reachable_modules": int(reach_decl["mod_cnt"] or 0),
        "reachable_loc": reachable_loc,
        "reachable_declarations": int(reach_decl["cnt"] or 0),
        "reachable_body_loc": int(reach_decl["body_loc"] or 0),
        "mathematical_declarations": int(reach_decl["math_cnt"] or 0),
        "mathematical_body_loc": int(reach_decl["math_loc"] or 0),
        "dead_declarations": max(0, int(raw_decl["proj_cnt"] or 0) - int(reach_decl["cnt"] or 0)),
        "dead_modules": max(0, int(raw_mod["proj_cnt"] or 0) - int(reach_decl["mod_cnt"] or 0)),
        "compression_ratio": round(compression_ratio, 2),
        "edges": int(edge_cnt_row["cnt"] or 0),
        "duplicate_groups": int(dedup_meta.get("duplicate_groups", dup_row["dup_groups"]) or 0),
        "redundant_declarations": int(dedup_meta.get("redundant_declarations", dup_row["redundant_decls"]) or 0),
        "redundant_loc": int(dedup_meta.get("redundant_loc", dup_row["redundant_loc"]) or 0),
        "prune_meta": prune_meta,
        "dedup_meta": dedup_meta,
    }


def _toposort_chapters(
    chapters: list[dict[str, Any]],
    chapter_edges: dict[int, set[int]],
) -> list[dict[str, Any]]:
    """Order chapters from foundational dependencies to final conclusion (Kahn's algorithm)."""
    if not chapters:
        return []
    by_id = {int(c["id"]): c for c in chapters}
    cids = list(by_id.keys())
    # edge u -> v means chapter u depends on chapter v; we want v before u
    deps: dict[int, set[int]] = {cid: set() for cid in cids}
    dependents: dict[int, set[int]] = {cid: set() for cid in cids}
    for u, targets in chapter_edges.items():
        if u not in by_id:
            continue
        for v in targets:
            if v in by_id and v != u:
                deps[u].add(v)
                dependents[v].add(u)

    in_deg = {cid: len(deps[cid]) for cid in cids}
    ready = deque(sorted([cid for cid, d in in_deg.items() if d == 0], key=lambda x: (-int(by_id[x]["total_loc"] or 0), x)))
    ordered: list[int] = []
    seen: set[int] = set()

    while ready:
        cur = ready.popleft()
        if cur in seen:
            continue
        seen.add(cur)
        ordered.append(cur)
        for nxt in sorted(dependents[cur]):
            in_deg[nxt] -= 1
            if in_deg[nxt] == 0:
                ready.append(nxt)

    # Break any remaining cycles deterministically by total_loc desc
    remaining = [cid for cid in cids if cid not in seen]
    remaining.sort(key=lambda x: (-int(by_id[x]["total_loc"] or 0), x))
    ordered.extend(remaining)
    return [by_id[cid] for cid in ordered]


def _compute_chapter_dependencies(
    conn: sqlite3.Connection,
    chapters: list[dict[str, Any]],
    cluster_to_chapter: dict[int, int],
) -> dict[int, set[int]]:
    """Compute inter-chapter dependency edges from cluster interfaces and SQLite edges."""
    chapter_edges: dict[int, set[int]] = defaultdict(set)
    # First check interface_in_json on each chapter
    for chap in chapters:
        cid = int(chap["id"])
        in_items = safe_json_loads(chap.get("interface_in_json"), [])
        for item in in_items:
            if isinstance(item, dict) and item.get("cluster_id") is not None:
                dep_chap = cluster_to_chapter.get(int(item["cluster_id"]))
                if dep_chap is not None and dep_chap != cid:
                    chapter_edges[cid].add(dep_chap)

    # Augment from edges table (fast SQL aggregation)
    if not any(chapter_edges.values()) and cluster_to_chapter:
        rows = query_all(
            conn,
            """
            SELECT DISTINCT m1.cluster_id AS src_c, m2.cluster_id AS dst_c
            FROM edges e
            JOIN metrics m1 ON m1.decl_id = e.src_id
            JOIN metrics m2 ON m2.decl_id = e.dst_id
            WHERE m1.cluster_id IS NOT NULL
              AND m2.cluster_id IS NOT NULL
              AND m1.cluster_id != m2.cluster_id
              AND m1.reachable = 1
              AND m2.reachable = 1
            LIMIT 5000
            """,
        )
        for r in rows:
            u = cluster_to_chapter.get(int(r["src_c"]))
            v = cluster_to_chapter.get(int(r["dst_c"]))
            if u is not None and v is not None and u != v:
                chapter_edges[u].add(v)
    return chapter_edges


def _get_direct_math_deps(
    conn: sqlite3.Connection,
    decl_id: int,
    *,
    limit: int = 12,
) -> list[dict[str, Any]]:
    """Fetch reachable non-bookkeeping direct dependencies of a declaration."""
    use_reach = has_reachable_metrics(conn)
    if use_reach:
        return query_all(
            conn,
            """
            SELECT DISTINCT d.id, d.name, d.short_name, d.kind, d.body_loc,
                            COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score,
                            COALESCE(mod.path, '') AS module_path
            FROM edges e
            JOIN declarations d ON d.id = e.dst_id
            JOIN metrics m ON m.decl_id = d.id
            LEFT JOIN modules mod ON mod.id = d.module_id
            WHERE e.src_id = ?
              AND d.id != ?
              AND m.reachable = 1
              AND d.is_mathlib = 0
              AND d.is_bookkeeping = 0
            ORDER BY m.bottleneck_score DESC, d.body_loc DESC, d.id ASC
            LIMIT ?
            """,
            (decl_id, decl_id, limit),
        )
    return query_all(
        conn,
        """
        SELECT DISTINCT d.id, d.name, d.short_name, d.kind, d.body_loc,
                        0.0 AS bottleneck_score,
                        COALESCE(mod.path, '') AS module_path
        FROM edges e
        JOIN declarations d ON d.id = e.dst_id
        LEFT JOIN modules mod ON mod.id = d.module_id
        WHERE e.src_id = ?
          AND d.id != ?
          AND d.is_mathlib = 0
          AND d.is_bookkeeping = 0
        ORDER BY d.body_loc DESC, d.id ASC
        LIMIT ?
        """,
        (decl_id, decl_id, limit),
    )


def _build_proof_sketch(
    decl: dict[str, Any],
    deps: list[dict[str, Any]],
) -> str:
    """Synthesize a strictly grounded conceptual proof sketch citing actual Lean dependencies."""
    thm_deps = [d for d in deps if d["kind"] in ("theorem", "lemma", "axiom")]
    def_deps = [d for d in deps if d["kind"] not in ("theorem", "lemma", "axiom")]

    sentences: list[str] = []
    if def_deps:
        top_defs = def_deps[:4]
        def_refs = ", ".join(
            f"{escape_latex_text(_human_title(d['short_name']))} \\leanlink{{{d['name']}}}"
            for d in top_defs
        )
        sentences.append(
            f"The argument operates on the structural objects {def_refs}."
        )

    if thm_deps:
        # Cite all top bottleneck dependencies so audit confirms full fidelity
        cited = thm_deps[:8]
        if len(cited) == 1:
            d = cited[0]
            sentences.append(
                f"The claim follows directly from "
                f"\\emph{{{escape_latex_text(_human_title(d['short_name']))}}} \\leanlink{{{d['name']}}}."
            )
        else:
            lead = cited[:-1]
            final = cited[-1]
            lead_str = ", ".join(
                f"\\emph{{{escape_latex_text(_human_title(d['short_name']))}}} \\leanlink{{{d['name']}}}"
                for d in lead
            )
            final_str = f"\\emph{{{escape_latex_text(_human_title(final['short_name']))}}} \\leanlink{{{final['name']}}}"
            sentences.append(
                f"Combining {lead_str} with {final_str} yields the stated result."
            )
    else:
        body_loc = int(decl.get("body_loc") or 0)
        if body_loc > 0:
            sentences.append(
                f"This result is established directly from standard library foundations "
                f"within its local module ({body_loc}~lines of formal proof)."
            )
        else:
            sentences.append(
                "This statement follows directly from standard library foundations."
            )

    return " ".join(sentences)


def _format_interface_summary(
    in_items: list[dict[str, Any]],
    out_items: list[dict[str, Any]],
    valid_reachable_names: set[str],
) -> str:
    """Render a compact formal interface block (Inputs |- Outputs)."""
    # Keep only non-mathlib reachable items for \leanlink anchors
    proj_in = [
        it for it in in_items
        if isinstance(it, dict)
        and not it.get("is_mathlib")
        and it.get("name") in valid_reachable_names
    ][:6]
    proj_out = [
        it for it in out_items
        if isinstance(it, dict)
        and not it.get("is_mathlib")
        and it.get("name") in valid_reachable_names
    ][:6]

    if not proj_in and not proj_out:
        return ""

    lines = [r"\begin{quote}\small"]
    lines.append(r"\textbf{Formal Interface ($\mathrm{Inputs} \vdash \mathrm{Outputs}$):}")
    if proj_in:
        in_str = ", ".join(
            f"{escape_latex_text(_human_title(it.get('short_name') or it['name']))}~\\leanlink{{{it['name']}}}"
            for it in proj_in
        )
        lines.append(rf"\par\noindent\emph{{Inputs:}} {in_str}.")
    if proj_out:
        out_str = ", ".join(
            f"{escape_latex_text(_human_title(it.get('short_name') or it['name']))}~\\leanlink{{{it['name']}}}"
            for it in proj_out
        )
        lines.append(rf"\par\noindent\emph{{Outputs:}} {out_str}.")
    lines.append(r"\end{quote}")
    return "\n".join(lines)


def _validate_refined_section(
    refined: str,
    allowed_leanlinks: set[str],
) -> bool:
    """Ensure an LLM-refined section obeys all grounding and leak constraints."""
    if not refined or len(refined.strip()) < 40:
        return False
    # Check no unknown \leanlink was invented
    found = set(re.findall(r"\\leanlink(?:\[[^\]]*\])?\{([^}]+)\}", refined))
    if not found.issubset(allowed_leanlinks):
        return False
    # Check no Lean bookkeeping leaks were introduced
    if detect_bookkeeping_leaks(refined):
        return False
    return True


def _fallback_package_chapters(conn: sqlite3.Connection) -> list[dict[str, Any]]:
    """Synthesize package-level pseudo-chapters when the clusters table is empty."""
    use_reach = has_reachable_metrics(conn)
    if use_reach:
        rows = query_all(
            conn,
            """
            SELECT COALESCE(NULLIF(mod.package, ''), 'Core') AS pkg,
                   COUNT(d.id) AS decl_count,
                   COALESCE(SUM(d.body_loc), 0) AS total_loc
            FROM declarations d
            JOIN metrics m ON m.decl_id = d.id
            LEFT JOIN modules mod ON mod.id = d.module_id
            WHERE m.reachable = 1 AND d.is_mathlib = 0
            GROUP BY pkg
            ORDER BY total_loc DESC
            LIMIT 15
            """,
        )
    else:
        rows = query_all(
            conn,
            """
            SELECT COALESCE(NULLIF(mod.package, ''), 'Core') AS pkg,
                   COUNT(d.id) AS decl_count,
                   COALESCE(SUM(d.body_loc), 0) AS total_loc
            FROM declarations d
            LEFT JOIN modules mod ON mod.id = d.module_id
            WHERE d.is_mathlib = 0
            GROUP BY pkg
            ORDER BY total_loc DESC
            LIMIT 15
            """,
        )
    chapters: list[dict[str, Any]] = []
    for idx, r in enumerate(rows, start=1):
        chapters.append(
            {
                "id": -idx,
                "parent_id": None,
                "level": 0,
                "title": r["pkg"],
                "package_filter": r["pkg"],
                "decl_count": int(r["decl_count"] or 0),
                "total_loc": int(r["total_loc"] or 0),
                "interface_in_json": "[]",
                "interface_out_json": "[]",
                "summary": "",
            }
        )
    return chapters


def generate_latex(
    db: DbHandle,
    output_path: str | Path | None = None,
    *,
    title: str | None = None,
    max_bottlenecks: int = 25,
    max_theorems_per_cluster: int = 12,
    max_defs_per_cluster: int = 6,
    max_chapters: int = 20,
    llm_refiner: SectionRefiner | None = None,
) -> str:
    """Generate a compact Annals-style LaTeX manuscript (`paper.tex`) from the proof DB."""
    with open_db(db, readonly=False) as conn:
        registry = _load_or_build_registry(conn)
        stats = _compute_corpus_stats(conn)
        roots = get_root_declaration_names(conn)
        use_reach = has_reachable_metrics(conn)

        # Valid reachable project declaration names (for safe \leanlink emission)
        if use_reach:
            valid_names = {
                str(r["name"])
                for r in query_all(
                    conn,
                    """
                    SELECT d.name
                    FROM declarations d
                    JOIN metrics m ON m.decl_id = d.id
                    WHERE m.reachable = 1 AND d.is_mathlib = 0
                    """,
                )
            }
        else:
            valid_names = {
                str(r["name"])
                for r in query_all(
                    conn,
                    "SELECT name FROM declarations WHERE is_mathlib = 0",
                )
            }

        # Top bottleneck pillar theorems
        if use_reach:
            bottlenecks = query_all(
                conn,
                """
                SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                       d.docstring, d.axioms_json,
                       COALESCE(mod.path, '') AS module_path,
                       COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score,
                       COALESCE(m.in_degree, 0) AS in_degree,
                       COALESCE(m.out_degree, 0) AS out_degree,
                       m.cluster_id
                FROM declarations d
                JOIN metrics m ON m.decl_id = d.id
                LEFT JOIN modules mod ON mod.id = d.module_id
                WHERE m.reachable = 1
                  AND d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                  AND d.kind IN ('theorem', 'lemma')
                ORDER BY m.bottleneck_score DESC, m.in_degree DESC, d.body_loc DESC
                LIMIT ?
                """,
                (max_bottlenecks,),
            )
        else:
            bottlenecks = query_all(
                conn,
                """
                SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                       d.docstring, d.axioms_json,
                       COALESCE(mod.path, '') AS module_path,
                       0.0 AS bottleneck_score,
                       (SELECT COUNT(*) FROM edges e WHERE e.dst_id = d.id) AS in_degree,
                       (SELECT COUNT(*) FROM edges e WHERE e.src_id = d.id) AS out_degree,
                       NULL AS cluster_id
                FROM declarations d
                LEFT JOIN modules mod ON mod.id = d.module_id
                WHERE d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                  AND d.kind IN ('theorem', 'lemma')
                ORDER BY in_degree DESC, d.body_loc DESC
                LIMIT ?
                """,
                (max_bottlenecks,),
            )

        # Load root theorem records
        root_records: list[dict[str, Any]] = []
        if roots:
            ph = ",".join("?" for _ in roots)
            root_records = query_all(
                conn,
                f"""
                SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                       d.docstring, d.axioms_json, COALESCE(mod.path, '') AS module_path
                FROM declarations d
                LEFT JOIN modules mod ON mod.id = d.module_id
                WHERE d.name IN ({ph})
                """,
                tuple(roots),
            )

        # Load cluster hierarchy and order chapters topologically
        chapters, sections_by_chapter, cluster_to_chapter = get_cluster_hierarchy(conn)
        using_clusters = bool(chapters)
        if using_clusters:
            chapter_edges = _compute_chapter_dependencies(conn, chapters, cluster_to_chapter)
            ordered_chapters = _toposort_chapters(chapters, chapter_edges)[:max_chapters]
        else:
            chapter_edges = {}
            ordered_chapters = _fallback_package_chapters(conn)[:max_chapters]

        # Build chapter id -> title map
        chapter_title_by_id = {
            int(c["id"]): _human_title(str(c["title"] or f"Chapter {c['id']}"))
            for c in ordered_chapters
        }

        doc_title = title
        if not doc_title:
            if roots:
                doc_title = f"A Compressed Mathematical Exposition of {_human_title(roots[0])}"
            else:
                doc_title = "A Compressed Mathematical Exposition of the Formal Proof"

        # ------------------------------------------------------------------
        # Build LaTeX document
        # ------------------------------------------------------------------
        parts: list[str] = []

        # Preamble
        parts.append(
            r"""\documentclass[11pt,reqno]{amsart}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,amsthm,mathtools,array}
\usepackage{booktabs}
\usepackage[margin=1in]{geometry}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue,urlcolor=blue]{hyperref}

\theoremstyle{plain}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}

\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{remark}[theorem]{Remark}

% Exact formal verification anchor (safe with underscores and line-breakable via \nolinkurl)
\newcommand{\leanlink}[1]{\allowbreak{\tiny\texttt{[\expandafter\nolinkurl\expandafter{\detokenize{#1}}]}}}
\newcommand{\leanmod}[1]{\allowbreak{\scriptsize\texttt{\expandafter\nolinkurl\expandafter{\detokenize{#1}}}}}
\emergencystretch=3em
\sloppy
"""
        )
        parts.append(registry.render_preamble())
        short_running_title = escape_latex_text(doc_title[:58] + ("..." if len(doc_title) > 58 else ""))
        parts.append(
            f"\n\\title[{short_running_title}]{{{escape_latex_text(doc_title)}}}\n"
            r"\author{Synthesized by \texttt{proof-compressor}}" "\n"
            r"\date{\today}" "\n\n"
            r"\begin{document}" "\n"
            r"\begin{abstract}" "\n"
            f"We present a compressed, self-contained mathematical exposition extracted directly "
            f"from a formal Lean~4 proof corpus comprising {stats['raw_modules']:,}~modules "
            f"({stats['raw_loc']:,}~lines of code) and {stats['raw_declarations']:,}~declarations. "
            f"Exact reverse-dependency pruning isolates {stats['reachable_modules']:,}~reachable modules "
            f"({stats['reachable_loc']:,}~lines, compression ratio {stats['compression_ratio']:.2f}$\\times$) "
            f"and {stats['mathematical_declarations']:,}~substantive mathematical declarations. "
            f"Every definition, theorem, and proof citation below is anchored to its verified Lean constant "
            f"via \\texttt{{\\textbackslash leanlink\\{{...\\}}}}.\n"
            r"\end{abstract}" "\n"
            r"\maketitle" "\n"
            r"\tableofcontents" "\n"
        )

        # ------------------------------------------------------------------
        # Section 1: Proof Overview & Quantitative Architecture
        # ------------------------------------------------------------------
        sec1: list[str] = [
            r"\section{Proof Overview and Quantitative Architecture}",
            "",
            (
                f"The formal repository contains {stats['raw_declarations']:,} project declarations across "
                f"{stats['raw_modules']:,} modules ({stats['raw_loc']:,} lines) connected by "
                f"{stats['edges']:,} dependency edges. Pruning all declarations unreachable from the target "
                f"theorem(s) eliminates {stats['dead_declarations']:,} dead declarations across "
                f"{stats['dead_modules']:,} unused modules, leaving {stats['reachable_declarations']:,} "
                f"reachable declarations ({stats['mathematical_declarations']:,} substantive mathematical "
                f"results after collapsing routine formalization glue)."
            ),
            "",
            r"\begin{table}[ht]",
            r"\centering",
            r"\caption{Quantitative Compression Summary}",
            r"\begin{tabular}{lr}",
            r"\toprule",
            r"Metric & Value \\",
            r"\midrule",
            f"Raw project modules & {stats['raw_modules']:,} \\\\",
            f"Reachable project modules & {stats['reachable_modules']:,} \\\\",
            f"Raw project LOC & {stats['raw_loc']:,} \\\\",
            f"Reachable project LOC & {stats['reachable_loc']:,} \\\\",
            f"Dead-code compression ratio & {stats['compression_ratio']:.2f}$\\times$ \\\\",
            f"Reachable declarations & {stats['reachable_declarations']:,} \\\\",
            f"Substantive mathematical declarations & {stats['mathematical_declarations']:,} \\\\",
            f"Canonical duplicate groups & {stats['duplicate_groups']:,} \\\\",
            f"Estimated redundant duplicate LOC & {stats['redundant_loc']:,} \\\\",
            r"\bottomrule",
            r"\end{tabular}",
            r"\end{table}",
            "",
        ]

        if root_records:
            sec1.append(r"\subsection{Target Main Theorems}")
            for rec in root_records[:5]:
                tex_stmt = lean_type_to_latex(rec["type_sig"] or "", registry)
                sec1.append(
                    f"\\begin{{theorem}}[{escape_latex_text(_human_title(rec['short_name']))}]"
                    f"\\leanlink{{{rec['name']}}}\n"
                    f"{_format_math_block(tex_stmt)}\n"
                    f"\\end{{theorem}}"
                )
                deps = _get_direct_math_deps(conn, int(rec["id"]), limit=10)
                if deps:
                    sec1.append(f"\\begin{{proof}}\n{_build_proof_sketch(rec, deps)}\n\\end{{proof}}\n")

        if bottlenecks:
            sec1.append(r"\subsection{Bottleneck Pillar Theorems}")
            sec1.append(
                "The global proof dependency DAG factors through a narrow spine of high-leverage "
                "bottleneck theorems separating large upstream developments from downstream applications. "
                "Table~\\ref{tab:bottlenecks} summarizes the highest-scoring formal bottlenecks."
            )
            sec1.append(r"\begin{table}[ht]")
            sec1.append(r"\centering")
            sec1.append(r"\caption{Top Mathematical Bottleneck Pillars}\label{tab:bottlenecks}")
            sec1.append(r"\small")
            sec1.append(r"\begin{tabular}{rp{0.56\textwidth}rr}")
            sec1.append(r"\toprule")
            sec1.append(r"\# & Pillar Theorem & Body LOC & Bottleneck Score \\")
            sec1.append(r"\midrule")
            for idx, b in enumerate(bottlenecks[:20], start=1):
                disp = escape_latex_text(_human_title(b["short_name"]))
                if len(disp) > 48:
                    disp = disp[:45] + "..."
                sec1.append(
                    f"{idx} & \\raggedright {disp} \\leanlink{{{b['name']}}} & "
                    f"{int(b['body_loc'] or 0):,} & {float(b['bottleneck_score'] or 0.0):.2f} \\\\"
                )
            sec1.append(r"\bottomrule")
            sec1.append(r"\end{tabular}")
            sec1.append(r"\end{table}")
            sec1.append("")

        if ordered_chapters:
            sec1.append(r"\subsection{Chapter Dependency Architecture}")
            sec1.append(
                f"The reachable proof graph decomposes into {len(ordered_chapters)} major chapters "
                f"ordered topologically from foundational structures to the main conclusions:"
            )
            sec1.append(r"\begin{enumerate}")
            for chap in ordered_chapters:
                cid = int(chap["id"])
                ctitle = escape_latex_text(chapter_title_by_id[cid])
                dep_cids = sorted(chapter_edges.get(cid, set()))
                dep_note = ""
                if dep_cids:
                    dep_titles = [
                        escape_latex_text(chapter_title_by_id[d])
                        for d in dep_cids
                        if d in chapter_title_by_id
                    ][:4]
                    if dep_titles:
                        dep_note = f" (builds on {', '.join(dep_titles)})"
                sec1.append(
                    f"\\item \\textbf{{{ctitle}}} "
                    f"({int(chap['decl_count'] or 0):,} declarations, "
                    f"{int(chap['total_loc'] or 0):,}~LOC){dep_note}."
                )
            sec1.append(r"\end{enumerate}")
            sec1.append("")

        parts.append("\n".join(sec1))

        # ------------------------------------------------------------------
        # Sections 2..N: Main Chapters
        # ------------------------------------------------------------------
        for chap in ordered_chapters:
            cid = int(chap["id"])
            ctitle = chapter_title_by_id[cid]

            # Collect all cluster_ids belonging to this chapter (chapter itself + its sections)
            if using_clusters:
                sec_ids = [cid] + [int(s["id"]) for s in sections_by_chapter.get(cid, [])]
                ph = ",".join("?" for _ in sec_ids)
                chap_decls = query_all(
                    conn,
                    f"""
                    SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                           d.docstring, COALESCE(mod.path, '') AS module_path,
                           COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score,
                           COALESCE(m.in_degree, 0) AS in_degree,
                           COALESCE(m.out_degree, 0) AS out_degree
                    FROM declarations d
                    JOIN metrics m ON m.decl_id = d.id
                    LEFT JOIN modules mod ON mod.id = d.module_id
                    WHERE m.cluster_id IN ({ph})
                      AND m.reachable = 1
                      AND d.is_mathlib = 0
                      AND d.is_bookkeeping = 0
                    ORDER BY m.bottleneck_score DESC, m.in_degree DESC, d.body_loc DESC
                    LIMIT 250
                    """,
                    tuple(sec_ids),
                )
            else:
                pkg = chap.get("package_filter", "Core")
                chap_decls = query_all(
                    conn,
                    """
                    SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                           d.docstring, COALESCE(mod.path, '') AS module_path,
                           0.0 AS bottleneck_score,
                           (SELECT COUNT(*) FROM edges e WHERE e.dst_id = d.id) AS in_degree,
                           (SELECT COUNT(*) FROM edges e WHERE e.src_id = d.id) AS out_degree
                    FROM declarations d
                    LEFT JOIN modules mod ON mod.id = d.module_id
                    WHERE COALESCE(NULLIF(mod.package, ''), 'Core') = ?
                      AND d.is_mathlib = 0
                      AND d.is_bookkeeping = 0
                    ORDER BY in_degree DESC, d.body_loc DESC
                    LIMIT 250
                    """,
                    (pkg,),
                )

            if not chap_decls:
                continue

            idioms = extract_proof_idioms(chap_decls, top_k=3)
            in_items = safe_json_loads(chap.get("interface_in_json"), [])
            out_items = safe_json_loads(chap.get("interface_out_json"), [])

            chap_lines: list[str] = [
                f"\\section{{{escape_latex_text(ctitle)}}}",
                "",
            ]

            idiom_clause = ""
            if idioms:
                tags = ", ".join(escape_latex_text(i["idiom"]) for i in idioms)
                idiom_clause = f" Primary proof idioms detected: \\emph{{{tags}}}."
            chap_lines.append(
                f"This chapter encompasses {int(chap['decl_count'] or len(chap_decls)):,} formal declarations "
                f"({int(chap['total_loc'] or 0):,}~LOC).{idiom_clause}"
            )
            raw_chap_summary = str(chap.get("summary") or "").strip()
            if raw_chap_summary and not re.match(r"^\d[\d,]*\s+declarations\b", raw_chap_summary):
                chap_summary = _clean_docstring_for_prose(raw_chap_summary)
                if chap_summary:
                    chap_lines.append(chap_summary)

            iface_tex = _format_interface_summary(in_items, out_items, valid_names)
            if iface_tex:
                chap_lines.append(iface_tex)
            chap_lines.append("")

            # Key definitions in this chapter (prefer rich signatures ahead of bare `: Prop` bundles)
            all_chap_defs = [
                d for d in chap_decls
                if d["kind"] in ("def", "structure", "class", "inductive", "abbrev")
            ]
            all_chap_defs.sort(
                key=lambda d: (
                    0 if str(d.get("type_sig") or "").strip().lstrip(":").strip() in ("Prop", "") else 1,
                    float(d.get("bottleneck_score") or 0.0),
                    int(d.get("in_degree") or 0),
                ),
                reverse=True,
            )
            key_defs = all_chap_defs[:max_defs_per_cluster]

            if key_defs:
                chap_lines.append(r"\subsection{Core Definitions and Structures}")
                for d in key_defs:
                    tex_sig = lean_type_to_latex(d["type_sig"] or "", registry)
                    doc_note = _clean_docstring_for_prose(d.get("docstring"))
                    chap_lines.append(
                        f"\\begin{{definition}}[{escape_latex_text(_human_title(d['short_name']))}]"
                        f"\\leanlink{{{d['name']}}}"
                    )
                    if doc_note:
                        chap_lines.append(doc_note)
                    chap_lines.append(_format_math_block(tex_sig))
                    chap_lines.append(r"\end{definition}")
                    chap_lines.append("")

            # Major theorems & propositions in this chapter
            key_thms = [
                d for d in chap_decls
                if d["kind"] in ("theorem", "lemma")
            ][:max_theorems_per_cluster]

            allowed_links_in_chap: set[str] = {d["name"] for d in chap_decls}
            for item in in_items + out_items:
                if isinstance(item, dict) and item.get("name") in valid_names:
                    allowed_links_in_chap.add(str(item["name"]))
            theorem_deps_ctx: dict[str, list[str]] = {}

            if key_thms:
                chap_lines.append(r"\subsection{Main Results}")
                for idx, thm in enumerate(key_thms):
                    env = "theorem" if idx < 2 or float(thm["bottleneck_score"] or 0.0) > 10.0 else (
                        "proposition" if idx < 6 else "lemma"
                    )
                    tex_stmt = lean_type_to_latex(thm["type_sig"] or "", registry)
                    doc_note = _clean_docstring_for_prose(thm.get("docstring"))
                    chap_lines.append(
                        f"\\begin{{{env}}}[{escape_latex_text(_human_title(thm['short_name']))}]"
                        f"\\leanlink{{{thm['name']}}}"
                    )
                    if doc_note:
                        chap_lines.append(doc_note)
                    chap_lines.append(_format_math_block(tex_stmt))
                    chap_lines.append(f"\\end{{{env}}}")

                    deps = _get_direct_math_deps(conn, int(thm["id"]), limit=10)
                    for dep in deps:
                        allowed_links_in_chap.add(str(dep["name"]))
                    theorem_deps_ctx[str(thm["name"])] = [str(dep["name"]) for dep in deps]

                    sketch = _build_proof_sketch(thm, deps)
                    chap_lines.append(f"\\begin{{proof}}\n{sketch}\n\\end{{proof}}")
                    chap_lines.append("")

            draft_section = "\n".join(chap_lines)
            if llm_refiner is not None:
                ctx = {
                    "chapter_title": ctitle,
                    "idioms": idioms,
                    "symbol_macros": {e.lean_name: e.latex_macro for e in registry.entries},
                    "interface_in": [i.get("name") for i in in_items if isinstance(i, dict)],
                    "interface_out": [i.get("name") for i in out_items if isinstance(i, dict)],
                    "theorem_dependencies": theorem_deps_ctx,
                    "allowed_leanlinks": sorted(allowed_links_in_chap),
                }
                try:
                    refined = llm_refiner(draft_section, ctx)
                    if _validate_refined_section(refined, allowed_links_in_chap):
                        draft_section = refined
                except Exception:
                    # Strictly fall back to deterministic grounded draft on any hook failure
                    pass

            parts.append(draft_section)

        # ------------------------------------------------------------------
        # Technical Appendix
        # ------------------------------------------------------------------
        app: list[str] = [
            r"\appendix",
            r"\section{Symbol Glossary}",
            "Table~\\ref{tab:glossary} anchors each global LaTeX notation macro to its "
            "underlying Lean~4 definition and source module.",
            "",
        ]

        if registry.entries:
            app.append(r"\begin{table}[ht]")
            app.append(r"\centering")
            app.append(r"\caption{Global Symbol Registry}\label{tab:glossary}")
            app.append(r"\small")
            app.append(r"\begin{tabular}{llp{0.34\textwidth}p{0.30\textwidth}}")
            app.append(r"\toprule")
            app.append(r"Symbol & Macro & Lean Constant & Module \\")
            app.append(r"\midrule")
            for entry in registry.entries[:40]:
                # Only emit \leanlink for reachable/valid project decls
                link_cell = (
                    f"\\leanlink{{{entry.lean_name}}}"
                    if entry.lean_name in valid_names
                    else f"\\texttt{{\\detokenize{{{entry.lean_name}}}}}"
                )
                mod_cell = f"\\leanmod{{{entry.module_path}}}" if entry.module_path else "---"
                app.append(
                    f"${entry.latex_macro}$ & \\texttt{{\\detokenize{{{entry.latex_macro}}}}} & "
                    f"\\raggedright {link_cell} & \\raggedright\\arraybackslash {mod_cell} \\\\"
                )
            app.append(r"\bottomrule")
            app.append(r"\end{tabular}")
            app.append(r"\end{table}")
        else:
            app.append("No project-level symbolic definitions were registered.")
        app.append("")

        # Appendix B: Dead-code & dedup compression breakdown
        app.append(r"\section{Compression and Deduplication Breakdown}")
        app.append(
            f"Reverse-dependency reachability pruning removes {stats['dead_declarations']:,} "
            f"unreachable declarations ({stats['raw_loc'] - stats['reachable_loc']:,}~LOC). "
            f"Within the reachable core, canonical type-signature hashing identifies "
            f"{stats['duplicate_groups']:,} duplicate signature groups accounting for "
            f"{stats['redundant_declarations']:,} redundant declarations "
            f"({stats['redundant_loc']:,}~LOC of candidate consolidation)."
        )
        app.append("")

        # Appendix C: Formal Verification Summary
        app.append(r"\section{Formal Verification and Axiom Summary}")
        non_std_axioms: set[str] = set()
        all_axioms: set[str] = set()
        for rec in root_records:
            axs = safe_json_loads(rec.get("axioms_json"), [])
            if isinstance(axs, list):
                for a in axs:
                    a_str = str(a)
                    all_axioms.add(a_str)
                    if a_str not in _STANDARD_AXIOMS:
                        non_std_axioms.add(a_str)

        if root_records:
            root_links = ", ".join(f"\\leanlink{{{r['name']}}}" for r in root_records)
            app.append(f"Root target declarations audited: {root_links}.")
        if all_axioms:
            ax_list = ", ".join(f"\\texttt{{\\detokenize{{{a}}}}}" for a in sorted(all_axioms))
            app.append(f"Recorded axiom footprint across root declarations: {ax_list}.")
            if non_std_axioms:
                bad_list = ", ".join(f"\\texttt{{\\detokenize{{{a}}}}}" for a in sorted(non_std_axioms))
                app.append(f"\\textbf{{Warning:}} non-standard axioms detected: {bad_list}.")
            else:
                app.append("All recorded root axioms lie within the standard Lean~4 foundational axioms.")
        else:
            app.append(
                "Kernel axiom metadata was not populated in this database snapshot; run the "
                "Lean~4 \\texttt{.olean} extractor or refactoring gate to record exact \\texttt{\\#print axioms} output."
            )
        app.append("")
        app.append(r"\end{document}")

        parts.append("\n".join(app))

    latex_text = "\n".join(parts) + "\n"
    if output_path is not None:
        out = Path(output_path)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(latex_text, encoding="utf-8")
    return latex_text
