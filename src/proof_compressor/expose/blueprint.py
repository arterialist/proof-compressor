"""Self-contained, zero-build interactive 3-zoom-level HTML proof map generator."""

from __future__ import annotations

import html
import json
import re
import sqlite3
from collections import defaultdict
from pathlib import Path
from typing import Any, Sequence

from proof_compressor.expose._db import (
    DbHandle,
    get_cluster_hierarchy,
    get_root_declaration_names,
    has_reachable_metrics,
    open_db,
    query_all,
    safe_json_loads,
)
from proof_compressor.expose.filter import extract_proof_idioms
from proof_compressor.expose.latex import (
    _compute_chapter_dependencies,
    _compute_corpus_stats,
    _fallback_package_chapters,
    _human_title,
    _load_or_build_registry,
    _toposort_chapters,
)
from proof_compressor.expose.symbols import lean_type_to_latex


def _safe_json_for_script(obj: Any) -> str:
    """Serialize JSON safely for embedding inside an HTML <script> tag."""
    raw = json.dumps(obj, ensure_ascii=False)
    return raw.replace("</", "<\\/").replace("<!--", "<\\!--")


def _extract_audit_status_by_const(audit_report: dict[str, Any] | None) -> dict[str, list[str]]:
    """Map Lean constant names to any audit warnings/errors recorded for them."""
    issues: dict[str, list[str]] = defaultdict(list)
    if not audit_report:
        return issues
    for it in audit_report.get("unknown_leanlinks", []):
        issues[str(it.get("constant", ""))].append("unknown constant")
    for it in audit_report.get("unreachable_leanlinks", []):
        issues[str(it.get("constant", ""))].append("unreachable from root")
    for it in audit_report.get("invented_citations", []):
        issues[str(it.get("theorem", ""))].append(f"non-DAG citation: {it.get('cited')}")
    for it in audit_report.get("omitted_bottlenecks", []):
        issues[str(it.get("theorem", ""))].append(f"omits bottleneck: {it.get('missing_dependency')}")
    for it in audit_report.get("dropped_hypotheses", []):
        issues[str(it.get("theorem", ""))].append("potential dropped hypothesis")
    return issues


def _clean_tex_snippet(text: str) -> str:
    """Convert a short LaTeX prose snippet into readable plain/KaTeX text for HTML cards."""
    s = re.sub(r"\\leanlink(?:\[[^\]]*\])?\{[^}]*\}", "", text)
    s = re.sub(r"\\leanmod\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\\label\{[^}]*\}", "", s)
    s = re.sub(r"\\ref\{([^}]*)\}", r"§\1", s)
    s = re.sub(r"\\textbf\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\\emph\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\\texttt\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def _parse_manuscript_chapters(
    conn: sqlite3.Connection,
    chapters_dir: str | Path,
    *,
    register_decl_fn: Any,
    manuscript_href: str | None = "manuscript.pdf",
    chapter_page_map: dict[int, int] | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, int]]]:
    """Parse hand-written `chNN_*.tex` chapters and resolve their anchored declarations."""
    cdir = Path(chapters_dir)
    paths = sorted(cdir.glob("ch[0-9][0-9]_*.tex"))
    if not paths:
        return [], []

    default_pages = {1: 1, 2: 7, 3: 15, 4: 21, 5: 26}
    pages = chapter_page_map if chapter_page_map is not None else default_pages

    sec_re = re.compile(r"\\section\{([^}]+)\}")
    sub_re = re.compile(r"\\subsection\{([^}]+)\}")
    link_re = re.compile(r"\\leanlink(?:\[[^\]]*\])?\{([^}]+)\}")
    thm_re = re.compile(
        r"\\begin\{(theorem|proposition|lemma|corollary|definition|maintheorem)\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}",
        re.S,
    )

    raw_chapters: list[dict[str, Any]] = []
    all_needed_names: list[str] = []
    seen_names: set[str] = set()

    for idx, p in enumerate(paths, start=1):
        txt = p.read_text(encoding="utf-8")
        sec_m = sec_re.search(txt)
        title = sec_m.group(1).strip() if sec_m else p.stem
        subs = [m.group(1).strip() for m in sub_re.finditer(txt)]
        links = list(dict.fromkeys(m.group(1).strip() for m in link_re.finditer(txt)))

        # Extract opening prose summary (lines between \label{sec:...} and first \subsection or \begin)
        body_start = sec_m.end() if sec_m else 0
        sub_m = sub_re.search(txt, body_start)
        intro_chunk = txt[body_start : sub_m.start()] if sub_m else txt[body_start : body_start + 1200]
        intro_paras = [
            _clean_tex_snippet(par)
            for par in intro_chunk.split("\n\n")
            if par.strip() and not par.strip().startswith(("\\label{", "%", "\\begin{", "\\end{"))
        ]
        summary = " ".join(intro_paras[:2])
        if len(summary) > 520:
            summary = summary[:517].rsplit(" ", 1)[0] + "..."

        # Prose word count
        prose = link_re.sub("", txt)
        prose = re.sub(r"\\leanmod\{[^}]*\}", "", prose)
        prose = re.sub(r"\\[A-Za-z]+\*?", " ", prose)
        word_count = len(re.findall(r"[A-Za-z0-9']+", prose))

        # Extract theorem environments and their primary \leanlink
        thm_entries: list[dict[str, str]] = []
        for tm in thm_re.finditer(txt):
            lm = link_re.search(tm.group(3))
            if lm is None:
                continue
            cname = lm.group(1).strip()
            thm_entries.append(
                {
                    "kind": tm.group(1),
                    "title": (tm.group(2) or "").strip(),
                    "name": cname,
                }
            )
            if cname not in seen_names:
                seen_names.add(cname)
                all_needed_names.append(cname)

        for cname in links:
            if cname not in seen_names:
                seen_names.add(cname)
                all_needed_names.append(cname)

        page_no = pages.get(idx)
        pdf_link = f"{manuscript_href}#page={page_no}" if (manuscript_href and page_no) else (manuscript_href or "")
        raw_chapters.append(
            {
                "id": idx,
                "order": idx - 1,
                "filename": p.name,
                "tex_href": f"chapters/{p.name}",
                "pdf_href": pdf_link,
                "page_no": page_no,
                "title": title,
                "subsections": subs,
                "summary": summary,
                "word_count": word_count,
                "line_count": len(txt.splitlines()),
                "links": links,
                "thm_entries": thm_entries,
            }
        )

    # Batch-fetch declaration rows from SQLite for all anchors in ch01..ch05
    name_to_id: dict[str, int] = {}
    if all_needed_names:
        for i in range(0, len(all_needed_names), 400):
            batch = all_needed_names[i : i + 400]
            ph = ",".join("?" for _ in batch)
            rows = query_all(
                conn,
                f"""
                SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                       d.docstring, d.start_line, d.end_line, d.axioms_json, d.is_bookkeeping,
                       COALESCE(mod.path, '') AS module_path,
                       COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score,
                       COALESCE(m.in_degree, 0) AS in_degree,
                       COALESCE(m.out_degree, 0) AS out_degree,
                       m.cluster_id
                FROM declarations d
                LEFT JOIN metrics m ON m.decl_id = d.id
                LEFT JOIN modules mod ON mod.id = d.module_id
                WHERE d.name IN ({ph})
                """,
                tuple(batch),
            )
            for r in rows:
                rec = register_decl_fn(r)
                name_to_id[rec["name"]] = rec["id"]

    manuscript_chapters: list[dict[str, Any]] = []
    for ch in raw_chapters:
        decl_ids: list[int] = []
        seen_ids: set[int] = set()
        for te in ch["thm_entries"]:
            did = name_to_id.get(te["name"])
            if did is not None and did not in seen_ids:
                seen_ids.add(did)
                decl_ids.append(did)
        all_link_ids = [name_to_id[nm] for nm in ch["links"] if nm in name_to_id]
        manuscript_chapters.append(
            {
                "id": ch["id"],
                "order": ch["order"],
                "filename": ch["filename"],
                "tex_href": ch["tex_href"],
                "pdf_href": ch["pdf_href"],
                "page_no": ch["page_no"],
                "title": ch["title"],
                "subsections": ch["subsections"],
                "summary": ch["summary"],
                "word_count": ch["word_count"],
                "line_count": ch["line_count"],
                "unique_links_count": len(ch["links"]),
                "theorem_entries": ch["thm_entries"],
                "decl_ids": decl_ids,
                "all_link_ids": all_link_ids,
            }
        )

    # Natural 5-chapter mathematical dependency DAG if there are 5 chapters
    edges: list[dict[str, int]] = []
    if len(manuscript_chapters) >= 5:
        edges = [
            {"from": 4, "to": 5},
            {"from": 4, "to": 2},
            {"from": 3, "to": 5},
            {"from": 3, "to": 2},
            {"from": 5, "to": 1},
            {"from": 2, "to": 1},
        ]
    else:
        for i in range(1, len(manuscript_chapters)):
            edges.append({"from": i, "to": i + 1})

    return manuscript_chapters, edges


def _build_blueprint_payload(
    conn: sqlite3.Connection,
    *,
    title: str | None = None,
    audit_report: dict[str, Any] | None = None,
    max_pillars: int = 30,
    max_chapters: int = 24,
    max_decls_per_chapter: int = 16,
    chapters_dir: str | Path | None = None,
    manuscript_href: str | None = None,
    readers_guide_href: str | None = None,
    overview: dict[str, Any] | None = None,
    chapter_page_map: dict[int, int] | None = None,
) -> dict[str, Any]:
    """Extract a compact JSON payload powering all three zoom levels of blueprint.html."""
    registry = _load_or_build_registry(conn)
    stats = _compute_corpus_stats(conn)
    roots = get_root_declaration_names(conn)
    use_reach = has_reachable_metrics(conn)
    audit_issues = _extract_audit_status_by_const(audit_report)

    doc_title = title or (
        f"Proof Map: {_human_title(roots[0])}" if roots else "Proof Compressor Blueprint"
    )

    chapters, sections_by_chapter, cluster_to_chapter = get_cluster_hierarchy(conn)
    using_clusters = bool(chapters)
    if using_clusters:
        chapter_edges_map = _compute_chapter_dependencies(conn, chapters, cluster_to_chapter)
        ordered_chapters = _toposort_chapters(chapters, chapter_edges_map)[:max_chapters]
    else:
        chapter_edges_map = {}
        ordered_chapters = _fallback_package_chapters(conn)[:max_chapters]

    # Top bottleneck pillars
    if use_reach:
        pillar_rows = query_all(
            conn,
            """
            SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                   d.docstring, d.start_line, d.end_line, d.axioms_json, d.is_bookkeeping,
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
            (max_pillars,),
        )
    else:
        pillar_rows = query_all(
            conn,
            """
            SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                   d.docstring, d.start_line, d.end_line, d.axioms_json, d.is_bookkeeping,
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
            (max_pillars,),
        )

    # Collect all declarations we want inspectable in Level 2 (pillars + chapter highlights + roots)
    decl_records_by_id: dict[int, dict[str, Any]] = {}

    def _register_decl(row: dict[str, Any], chapter_id: int | None = None) -> dict[str, Any]:
        did = int(row["id"])
        if did in decl_records_by_id:
            if chapter_id is not None and decl_records_by_id[did]["chapter_id"] is None:
                decl_records_by_id[did]["chapter_id"] = chapter_id
            return decl_records_by_id[did]

        name = str(row["name"])
        short_name = str(row["short_name"] or name.rsplit(".", 1)[-1])
        cid_raw = row.get("cluster_id")
        resolved_chap = chapter_id
        if resolved_chap is None and cid_raw is not None:
            resolved_chap = cluster_to_chapter.get(int(cid_raw), int(cid_raw))

        axioms = safe_json_loads(row.get("axioms_json"), [])
        if not isinstance(axioms, list):
            axioms = []

        rec = {
            "id": did,
            "name": name,
            "short_name": short_name,
            "display_title": _human_title(short_name),
            "kind": str(row["kind"] or "theorem"),
            "module_path": str(row.get("module_path") or ""),
            "start_line": int(row.get("start_line") or 0),
            "end_line": int(row.get("end_line") or 0),
            "body_loc": int(row.get("body_loc") or 0),
            "type_sig": str(row.get("type_sig") or ""),
            "latex_stmt": lean_type_to_latex(str(row.get("type_sig") or ""), registry),
            "docstring": str(row.get("docstring") or "").strip(),
            "bottleneck_score": round(float(row.get("bottleneck_score") or 0.0), 3),
            "in_degree": int(row.get("in_degree") or 0),
            "out_degree": int(row.get("out_degree") or 0),
            "chapter_id": resolved_chap,
            "is_bookkeeping": bool(row.get("is_bookkeeping")),
            "is_root": name in roots,
            "axioms": [str(a) for a in axioms],
            "audit_status": "issue" if name in audit_issues else ("verified" if audit_report else "unchecked"),
            "audit_notes": audit_issues.get(name, []),
            "deps": [],
            "dependents": [],
        }
        decl_records_by_id[did] = rec
        return rec

    pillar_ids: list[int] = []
    for pr in pillar_rows:
        rec = _register_decl(pr)
        pillar_ids.append(rec["id"])

    # Register roots too
    if roots:
        ph = ",".join("?" for _ in roots)
        root_rows = query_all(
            conn,
            f"""
            SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                   d.docstring, d.start_line, d.end_line, d.axioms_json, d.is_bookkeeping,
                   COALESCE(mod.path, '') AS module_path,
                   COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score,
                   COALESCE(m.in_degree, 0) AS in_degree,
                   COALESCE(m.out_degree, 0) AS out_degree,
                   m.cluster_id
            FROM declarations d
            LEFT JOIN metrics m ON m.decl_id = d.id
            LEFT JOIN modules mod ON mod.id = d.module_id
            WHERE d.name IN ({ph})
            """,
            tuple(roots),
        )
        for rr in root_rows:
            _register_decl(rr)

    # Build chapters payload
    chapters_payload: list[dict[str, Any]] = []
    ordered_chap_ids = {int(c["id"]) for c in ordered_chapters}

    for idx, chap in enumerate(ordered_chapters):
        cid = int(chap["id"])
        if using_clusters:
            sec_ids = [cid] + [int(s["id"]) for s in sections_by_chapter.get(cid, [])]
            ph = ",".join("?" for _ in sec_ids)
            rows = query_all(
                conn,
                f"""
                SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                       d.docstring, d.start_line, d.end_line, d.axioms_json, d.is_bookkeeping,
                       COALESCE(mod.path, '') AS module_path,
                       COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score,
                       COALESCE(m.in_degree, 0) AS in_degree,
                       COALESCE(m.out_degree, 0) AS out_degree,
                       m.cluster_id
                FROM declarations d
                JOIN metrics m ON m.decl_id = d.id
                LEFT JOIN modules mod ON mod.id = d.module_id
                WHERE m.cluster_id IN ({ph})
                  AND m.reachable = 1
                  AND d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                ORDER BY m.bottleneck_score DESC, m.in_degree DESC, d.body_loc DESC
                LIMIT ?
                """,
                (*sec_ids, max_decls_per_chapter),
            )
        else:
            pkg = chap.get("package_filter", "Core")
            rows = query_all(
                conn,
                """
                SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.body_loc,
                       d.docstring, d.start_line, d.end_line, d.axioms_json, d.is_bookkeeping,
                       COALESCE(mod.path, '') AS module_path,
                       0.0 AS bottleneck_score,
                       (SELECT COUNT(*) FROM edges e WHERE e.dst_id = d.id) AS in_degree,
                       (SELECT COUNT(*) FROM edges e WHERE e.src_id = d.id) AS out_degree,
                       NULL AS cluster_id
                FROM declarations d
                LEFT JOIN modules mod ON mod.id = d.module_id
                WHERE COALESCE(NULLIF(mod.package, ''), 'Core') = ?
                  AND d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                ORDER BY in_degree DESC, d.body_loc DESC
                LIMIT ?
                """,
                (pkg, max_decls_per_chapter),
            )

        idioms = extract_proof_idioms(rows, top_k=3)
        decl_ids_in_chap: list[int] = []
        for r in rows:
            rec = _register_decl(r, chapter_id=cid)
            decl_ids_in_chap.append(rec["id"])

        in_items = [
            {
                "name": str(it.get("name", "")),
                "short_name": str(it.get("short_name") or it.get("name", "")),
                "kind": str(it.get("kind", "")),
                "is_mathlib": bool(it.get("is_mathlib")),
            }
            for it in safe_json_loads(chap.get("interface_in_json"), [])
            if isinstance(it, dict) and it.get("name")
        ][:12]
        out_items = [
            {
                "name": str(it.get("name", "")),
                "short_name": str(it.get("short_name") or it.get("name", "")),
                "kind": str(it.get("kind", "")),
                "is_mathlib": bool(it.get("is_mathlib")),
            }
            for it in safe_json_loads(chap.get("interface_out_json"), [])
            if isinstance(it, dict) and it.get("name")
        ][:12]

        chapters_payload.append(
            {
                "id": cid,
                "order": idx,
                "title": _human_title(str(chap["title"] or f"Chapter {cid}")),
                "raw_title": str(chap["title"] or ""),
                "decl_count": int(chap["decl_count"] or len(rows)),
                "total_loc": int(chap["total_loc"] or 0),
                "summary": str(chap.get("summary") or ""),
                "idioms": [i["idiom"] for i in idioms],
                "interface_in": in_items,
                "interface_out": out_items,
                "decl_ids": decl_ids_in_chap,
                "depends_on": sorted(
                    d for d in chapter_edges_map.get(cid, set()) if d in ordered_chap_ids
                ),
            }
        )

    # Populate manuscript chapters if supplied (registering all anchored decls before edge lookup)
    manuscript_chapters: list[dict[str, Any]] = []
    manuscript_edges: list[dict[str, int]] = []
    if chapters_dir is not None:
        manuscript_chapters, manuscript_edges = _parse_manuscript_chapters(
            conn,
            chapters_dir,
            register_decl_fn=_register_decl,
            manuscript_href=manuscript_href or "manuscript.pdf",
            chapter_page_map=chapter_page_map,
        )

    # Populate direct dependencies / dependents for all registered Level-2 declarations
    reg_ids = list(decl_records_by_id.keys())
    if reg_ids:
        for i in range(0, len(reg_ids), 400):
            batch = reg_ids[i : i + 400]
            ph = ",".join("?" for _ in batch)
            dep_rows = query_all(
                conn,
                f"""
                SELECT DISTINCT e.src_id, d.id AS dst_id, d.name, d.short_name, d.kind
                FROM edges e
                JOIN declarations d ON d.id = e.dst_id
                WHERE e.src_id IN ({ph})
                  AND d.id != e.src_id
                  AND d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                LIMIT 4000
                """,
                tuple(batch),
            )
            for dr in dep_rows:
                rec = decl_records_by_id.get(int(dr["src_id"]))
                if rec is not None and len(rec["deps"]) < 20:
                    rec["deps"].append(
                        {
                            "id": int(dr["dst_id"]),
                            "name": str(dr["name"]),
                            "short_name": str(dr["short_name"] or dr["name"]),
                            "kind": str(dr["kind"] or ""),
                        }
                    )

            rev_rows = query_all(
                conn,
                f"""
                SELECT DISTINCT e.dst_id, d.id AS src_id, d.name, d.short_name, d.kind
                FROM edges e
                JOIN declarations d ON d.id = e.src_id
                WHERE e.dst_id IN ({ph})
                  AND d.id != e.dst_id
                  AND d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                LIMIT 4000
                """,
                tuple(batch),
            )
            for rr in rev_rows:
                rec = decl_records_by_id.get(int(rr["dst_id"]))
                if rec is not None and len(rec["dependents"]) < 20:
                    rec["dependents"].append(
                        {
                            "id": int(rr["src_id"]),
                            "name": str(rr["name"]),
                            "short_name": str(rr["short_name"] or rr["name"]),
                            "kind": str(rr["kind"] or ""),
                        }
                    )

    # Pillar-to-pillar direct edges (for Level 0 Pillar Spine DAG)
    pillar_id_set = set(pillar_ids)
    pillar_edges: list[dict[str, int]] = []
    if pillar_ids:
        ph = ",".join("?" for _ in pillar_ids)
        pe_rows = query_all(
            conn,
            f"""
            SELECT DISTINCT src_id, dst_id
            FROM edges
            WHERE src_id IN ({ph}) AND dst_id IN ({ph}) AND src_id != dst_id
            """,
            (*pillar_ids, *pillar_ids),
        )
        for pe in pe_rows:
            s, d = int(pe["src_id"]), int(pe["dst_id"])
            if s in pillar_id_set and d in pillar_id_set:
                # Arrow flows from dependency d -> dependent s (foundations to conclusion)
                pillar_edges.append({"from": d, "to": s})

    chapter_dag_edges: list[dict[str, int]] = []
    for ch in chapters_payload:
        for dep_cid in ch["depends_on"]:
            chapter_dag_edges.append({"from": dep_cid, "to": ch["id"]})

    symbols_payload = [
        {
            "macro": e.latex_macro,
            "math": e.math_definition,
            "lean_name": e.lean_name,
            "display_name": e.display_name,
            "module_path": e.module_path,
            "centrality": round(e.centrality, 2),
        }
        for e in registry.entries[:80]
    ]

    return {
        "title": doc_title,
        "roots": roots,
        "stats": {
            "raw_modules": stats["raw_modules"],
            "reachable_modules": stats["reachable_modules"],
            "raw_loc": stats["raw_loc"],
            "reachable_loc": stats["reachable_loc"],
            "raw_declarations": stats["raw_declarations"],
            "reachable_declarations": stats["reachable_declarations"],
            "mathematical_declarations": stats["mathematical_declarations"],
            "compression_ratio": stats["compression_ratio"],
            "duplicate_groups": stats["duplicate_groups"],
            "redundant_loc": stats["redundant_loc"],
            "edges": stats["edges"],
        },
        "audit": {
            "available": audit_report is not None,
            "passed": bool(audit_report.get("passed")) if audit_report else None,
            "fidelity_score": audit_report.get("fidelity_score") if audit_report else None,
            "summary": audit_report.get("summary", {}) if audit_report else {},
        },
        "chapters": chapters_payload,
        "chapter_edges": chapter_dag_edges,
        "manuscript_chapters": manuscript_chapters,
        "manuscript_edges": manuscript_edges,
        "overview": overview or {},
        "links": {
            "manuscript_href": manuscript_href or "",
            "readers_guide_href": readers_guide_href or "",
        },
        "pillar_ids": pillar_ids,
        "pillar_edges": pillar_edges,
        "declarations": list(decl_records_by_id.values()),
        "symbols": symbols_payload,
    }


_BLUEPRINT_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8" />
<meta name="viewport" content="width=device-width, initial-scale=1.0" />
<title>__TITLE__</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css" crossorigin="anonymous">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js" crossorigin="anonymous"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js" crossorigin="anonymous" onload="window.__renderAllMath && window.__renderAllMath()"></script>
<style>
  :root {
    --bg: #0d1117;
    --surface: #161b22;
    --surface-2: #1f2630;
    --border: #2c3543;
    --text: #e6edf3;
    --muted: #8b949e;
    --accent: #58a6ff;
    --accent-soft: rgba(88,166,255,0.14);
    --green: #3fb950;
    --amber: #d29922;
    --red: #f85149;
    --mono: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
    --sans: -apple-system, BlinkMacSystemFont, "Segoe UI", Inter, Roboto, sans-serif;
    --serif: Georgia, "Times New Roman", serif;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    background: var(--bg);
    color: var(--text);
    font-family: var(--sans);
    line-height: 1.5;
  }
  header {
    position: sticky;
    top: 0;
    z-index: 40;
    background: rgba(13,17,23,0.94);
    backdrop-filter: blur(8px);
    border-bottom: 1px solid var(--border);
    padding: 12px 20px;
  }
  .header-row {
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    justify-content: space-between;
    gap: 12px;
  }
  h1 {
    margin: 0;
    font-size: 1.1rem;
    font-weight: 600;
    letter-spacing: -0.01em;
  }
  .metrics-strip {
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
    margin-top: 10px;
  }
  .metric-card {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 5px 10px;
    font-size: 0.78rem;
  }
  .metric-card .lbl { color: var(--muted); margin-right: 6px; }
  .metric-card .val { font-family: var(--mono); font-weight: 600; color: var(--text); }
  .tabs {
    display: flex;
    gap: 6px;
  }
  .tab-btn {
    background: var(--surface);
    color: var(--muted);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 6px 12px;
    font-size: 0.82rem;
    cursor: pointer;
    transition: all 0.12s ease;
  }
  .tab-btn:hover { color: var(--text); border-color: var(--accent); }
  .tab-btn.active {
    background: var(--accent-soft);
    color: var(--accent);
    border-color: var(--accent);
    font-weight: 600;
  }
  main { padding: 18px 20px 48px; max-width: 1440px; margin: 0 auto; }
  .view { display: none; }
  .view.active { display: block; }

  /* Level 0: SVG DAG */
  .dag-toolbar {
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    justify-content: space-between;
    gap: 10px;
    margin-bottom: 10px;
  }
  .btn-group { display: flex; gap: 6px; }
  .ctrl-btn {
    background: var(--surface);
    color: var(--text);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 5px 10px;
    font-size: 0.8rem;
    cursor: pointer;
  }
  .ctrl-btn.active, .ctrl-btn:hover { border-color: var(--accent); color: var(--accent); }
  .dag-shell {
    position: relative;
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    height: 68vh;
    min-height: 440px;
    overflow: hidden;
  }
  #dag-svg { width: 100%; height: 100%; cursor: grab; display: block; }
  #dag-svg:active { cursor: grabbing; }
  .dag-node rect {
    rx: 8; ry: 8;
    fill: var(--surface-2);
    stroke: var(--border);
    stroke-width: 1.5;
    transition: stroke 0.12s;
  }
  .dag-node:hover rect { stroke: var(--accent); }
  .dag-node.root rect { stroke: var(--green); stroke-width: 2; }
  .dag-node text.node-title { fill: var(--text); font-size: 12px; font-weight: 600; }
  .dag-node text.node-meta { fill: var(--muted); font-size: 10px; font-family: var(--mono); }
  .dag-edge { fill: none; stroke: #48566a; stroke-width: 1.4; opacity: 0.72; }
  .dag-tooltip {
    position: absolute;
    pointer-events: none;
    background: rgba(13,17,23,0.96);
    border: 1px solid var(--accent);
    border-radius: 6px;
    padding: 8px 10px;
    font-size: 0.78rem;
    max-width: 320px;
    display: none;
    z-index: 20;
  }

  /* Level 1: Chapters */
  .chapter-grid { display: flex; flex-direction: column; gap: 16px; }
  .chapter-card {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 16px 18px;
  }
  .chapter-head {
    display: flex;
    flex-wrap: wrap;
    align-items: baseline;
    justify-content: space-between;
    gap: 8px;
    border-bottom: 1px solid var(--border);
    padding-bottom: 10px;
    margin-bottom: 12px;
  }
  .chapter-title { font-size: 1.05rem; font-weight: 600; margin: 0; }
  .badge {
    display: inline-block;
    font-size: 0.72rem;
    font-family: var(--mono);
    padding: 2px 7px;
    border-radius: 4px;
    border: 1px solid var(--border);
    background: var(--surface-2);
    color: var(--muted);
    margin-right: 4px;
  }
  .badge.idiom { color: #d2a8ff; border-color: rgba(210,168,255,0.35); }
  .badge.verified { color: var(--green); border-color: rgba(63,185,80,0.4); }
  .badge.issue { color: var(--red); border-color: rgba(248,81,73,0.4); }
  .badge.root { color: var(--amber); border-color: rgba(210,153,34,0.4); }
  details.iface-box {
    background: var(--surface-2);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 8px 12px;
    margin: 10px 0 14px;
    font-size: 0.84rem;
  }
  details.iface-box summary { cursor: pointer; font-weight: 600; color: var(--accent); }
  .iface-cols {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(260px, 1fr));
    gap: 12px;
    margin-top: 8px;
  }
  .stmt-item {
    border-left: 2px solid var(--border);
    padding: 6px 0 6px 12px;
    margin: 10px 0;
  }
  .stmt-item:hover { border-left-color: var(--accent); }
  .stmt-head {
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    gap: 8px;
    font-size: 0.86rem;
  }
  .stmt-link {
    color: var(--accent);
    cursor: pointer;
    font-family: var(--mono);
    font-size: 0.78rem;
    text-decoration: underline;
    background: none;
    border: none;
    padding: 0;
  }
  .math-box {
    font-family: var(--serif);
    background: rgba(255,255,255,0.02);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 8px 12px;
    margin-top: 6px;
    overflow-x: auto;
    font-size: 0.92rem;
  }

  /* Level 2: Inspector */
  .inspector-layout {
    display: grid;
    grid-template-columns: minmax(280px, 380px) 1fr;
    gap: 16px;
  }
  @media (max-width: 900px) {
    .inspector-layout { grid-template-columns: 1fr; }
  }
  .decl-list-panel, .decl-detail-panel {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 14px;
  }
  .search-input {
    width: 100%;
    background: var(--bg);
    color: var(--text);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 7px 10px;
    font-size: 0.85rem;
    margin-bottom: 10px;
  }
  .decl-list {
    max-height: 66vh;
    overflow-y: auto;
    display: flex;
    flex-direction: column;
    gap: 4px;
  }
  .decl-row {
    text-align: left;
    background: transparent;
    color: var(--text);
    border: 1px solid transparent;
    border-radius: 6px;
    padding: 7px 9px;
    cursor: pointer;
  }
  .decl-row:hover { background: var(--surface-2); }
  .decl-row.selected {
    background: var(--accent-soft);
    border-color: var(--accent);
  }
  .decl-row .nm { font-family: var(--mono); font-size: 0.8rem; word-break: break-all; }
  .decl-row .sub { font-size: 0.72rem; color: var(--muted); }
  pre.lean-code {
    background: var(--bg);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 10px 12px;
    font-family: var(--mono);
    font-size: 0.8rem;
    overflow-x: auto;
    white-space: pre-wrap;
    word-break: break-word;
  }
  .dep-chip {
    display: inline-block;
    background: var(--surface-2);
    border: 1px solid var(--border);
    color: var(--accent);
    border-radius: 4px;
    padding: 2px 7px;
    margin: 2px 4px 2px 0;
    font-family: var(--mono);
    font-size: 0.74rem;
    cursor: pointer;
  }
  .dep-chip:hover { border-color: var(--accent); }
  .overview-card {
    background: linear-gradient(135deg, rgba(88,166,255,0.08), rgba(63,185,80,0.06));
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 14px 18px;
    margin-bottom: 16px;
  }
  .overview-head {
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    justify-content: space-between;
    gap: 10px;
    margin-bottom: 8px;
  }
  .overview-links { display: flex; flex-wrap: wrap; gap: 8px; }
  .ext-link {
    display: inline-block;
    background: var(--surface-2);
    border: 1px solid var(--accent);
    color: var(--accent);
    border-radius: 6px;
    padding: 4px 10px;
    font-size: 0.78rem;
    font-weight: 600;
    text-decoration: none;
  }
  .ext-link:hover { background: var(--accent-soft); }
  .subsec-list {
    display: flex;
    flex-wrap: wrap;
    gap: 6px;
    margin: 8px 0 12px;
  }
  .subsec-pill {
    font-size: 0.76rem;
    background: var(--surface-2);
    border: 1px solid var(--border);
    border-radius: 999px;
    padding: 2px 10px;
    color: var(--text);
  }
</style>
</head>
<body>
<header>
  <div class="header-row">
    <h1 id="page-title">__TITLE__</h1>
    <div class="tabs">
      <button class="tab-btn active" data-level="0" onclick="switchLevel(0)">Level 0: Architecture DAG</button>
      <button class="tab-btn" data-level="1" onclick="switchLevel(1)">Level 1: Chapters</button>
      <button class="tab-btn" data-level="2" onclick="switchLevel(2)">Level 2: Lean Inspector</button>
    </div>
  </div>
  <div class="metrics-strip" id="metrics-strip"></div>
</header>

<main>
  <div id="overview-banner"></div>
  <!-- Level 0 -->
  <section id="view-0" class="view active">
    <div class="dag-toolbar">
      <div class="btn-group">
        <button id="mode-manuscript" class="ctrl-btn" style="display:none;" onclick="setDagMode('manuscript')">5-Chapter Proof Architecture</button>
        <button id="mode-chapters" class="ctrl-btn active" onclick="setDagMode('chapters')">Chapters DAG</button>
        <button id="mode-pillars" class="ctrl-btn" onclick="setDagMode('pillars')">Bottleneck Pillars Spine</button>
      </div>
      <div class="btn-group">
        <button class="ctrl-btn" onclick="zoomDag(1.2)">Zoom +</button>
        <button class="ctrl-btn" onclick="zoomDag(0.83)">Zoom -</button>
        <button class="ctrl-btn" onclick="resetDag()">Reset View</button>
      </div>
    </div>
    <div class="dag-shell">
      <svg id="dag-svg" xmlns="http://www.w3.org/2000/svg">
        <defs>
          <marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
            <path d="M 0 1 L 10 5 L 0 9 z" fill="#6e7f96" />
          </marker>
        </defs>
        <g id="dag-viewport"></g>
      </svg>
      <div id="dag-tooltip" class="dag-tooltip"></div>
    </div>
  </section>

  <!-- Level 1 -->
  <section id="view-1" class="view">
    <div style="margin-bottom:12px; display:flex; gap:10px; align-items:center; flex-wrap:wrap; justify-content:space-between;">
      <div style="display:flex; gap:10px; align-items:center; flex-wrap:wrap;">
        <input id="chapter-filter" class="search-input" style="max-width:340px; margin:0;" placeholder="Filter chapters or idioms..." oninput="renderChapters()" />
        <button class="ctrl-btn" onclick="clearChapterFilter()">Show All Chapters</button>
      </div>
      <div id="level1-mode-group" class="btn-group" style="display:none;">
        <button id="l1-manuscript" class="ctrl-btn active" onclick="setLevel1Mode('manuscript')">Manuscript Chapters (5)</button>
        <button id="l1-clusters" class="ctrl-btn" onclick="setLevel1Mode('clusters')">Lean Cluster Graph</button>
      </div>
    </div>
    <div id="chapter-grid" class="chapter-grid"></div>
  </section>

  <!-- Level 2 -->
  <section id="view-2" class="view">
    <div class="inspector-layout">
      <div class="decl-list-panel">
        <input id="decl-search" class="search-input" placeholder="Search Lean declaration, module, kind..." oninput="renderDeclList()" />
        <div id="decl-list" class="decl-list"></div>
      </div>
      <div class="decl-detail-panel" id="decl-detail">
        <p style="color:var(--muted);">Select a declaration on the left (or click any node in Level 0 / Level 1) to inspect its Lean signature, dependencies, axioms, and audit badges.</p>
      </div>
    </div>
  </section>
</main>

<script>
const PROOF_DATA = __PROOF_DATA_JSON__;

const DECL_BY_ID = new Map(PROOF_DATA.declarations.map(d => [d.id, d]));
const DECL_BY_NAME = new Map(PROOF_DATA.declarations.map(d => [d.name, d]));
const CHAPTER_BY_ID = new Map(PROOF_DATA.chapters.map(c => [c.id, c]));

const HAS_MANUSCRIPT = Array.isArray(PROOF_DATA.manuscript_chapters) && PROOF_DATA.manuscript_chapters.length > 0;
let dagMode = HAS_MANUSCRIPT ? "manuscript" : "chapters";
let level1Mode = HAS_MANUSCRIPT ? "manuscript" : "clusters";
let dagScale = 1.0;
let dagTx = 24;
let dagTy = 24;
let activeChapterFilterId = null;
let activeManuscriptChapterId = null;
let selectedDeclId = PROOF_DATA.pillar_ids[0] || (PROOF_DATA.declarations[0] && PROOF_DATA.declarations[0].id) || null;

function esc(s) {
  return String(s || "").replace(/[&<>"']/g, c => ({
    "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
  }[c]));
}

function fmtNum(n) {
  return Number(n || 0).toLocaleString();
}

window.__renderAllMath = function(rootEl) {
  if (typeof renderMathInElement === "function") {
    try {
      renderMathInElement(rootEl || document.body, {
        delimiters: [
          { left: "$$", right: "$$", display: true },
          { left: "\\[", right: "\\]", display: true },
          { left: "$", right: "$", display: false },
          { left: "\\(", right: "\\)", display: false }
        ],
        throwOnError: false
      });
    } catch (_e) {}
  }
};

function renderMetrics() {
  const s = PROOF_DATA.stats;
  const a = PROOF_DATA.audit;
  const auditVal = a.available
    ? `${a.passed ? "PASS" : "WARN"} (${(a.fidelity_score * 100).toFixed(1)}%)`
    : "Not Run";
  const cards = [
    ["Modules", `${fmtNum(s.reachable_modules)} / ${fmtNum(s.raw_modules)}`],
    ["LOC", `${fmtNum(s.reachable_loc)} / ${fmtNum(s.raw_loc)}`],
    ["Compression", `${s.compression_ratio}x`],
    ["Math Decls", fmtNum(s.mathematical_declarations)],
    ["Pillars", fmtNum(PROOF_DATA.pillar_ids.length)],
    ["Dup LOC", fmtNum(s.redundant_loc)],
    ["Audit", auditVal]
  ];
  document.getElementById("metrics-strip").innerHTML = cards.map(
    ([l, v]) => `<div class="metric-card"><span class="lbl">${esc(l)}</span><span class="val">${esc(v)}</span></div>`
  ).join("");
}

function switchLevel(level) {
  document.querySelectorAll(".view").forEach((el, idx) => {
    el.classList.toggle("active", idx === level);
  });
  document.querySelectorAll(".tab-btn").forEach(btn => {
    btn.classList.toggle("active", Number(btn.dataset.level) === level);
  });
  if (level === 0) renderDag();
  if (level === 1) renderChapters();
  if (level === 2) {
    renderDeclList();
    renderDeclDetail(selectedDeclId);
  }
}

function renderOverview() {
  const el = document.getElementById("overview-banner");
  const ov = PROOF_DATA.overview || {};
  const links = PROOF_DATA.links || {};
  if (!ov.headline && !HAS_MANUSCRIPT) {
    el.innerHTML = "";
    return;
  }
  const linkBtns = [
    links.readers_guide_href ? `<a class="ext-link" href="${esc(links.readers_guide_href)}" target="_blank">Reader's Guide (6 pp. PDF)</a>` : "",
    links.manuscript_href ? `<a class="ext-link" href="${esc(links.manuscript_href)}" target="_blank">Full Manuscript (35 pp. PDF)</a>` : ""
  ].filter(Boolean).join("");
  const bullets = Array.isArray(ov.pillars) && ov.pillars.length
    ? `<ul style="margin:6px 0 0; padding-left:18px; font-size:0.86rem; color:var(--text);">${ov.pillars.map(p => `<li>${esc(p)}</li>`).join("")}</ul>`
    : "";
  el.innerHTML = `
    <section class="overview-card">
      <div class="overview-head">
        <div>
          <strong style="font-size:0.96rem;">Big-Picture Proof Overview</strong>
          ${ov.headline ? `<span class="badge verified" style="margin-left:8px;">${esc(ov.headline)}</span>` : ""}
        </div>
        <div class="overview-links">${linkBtns}</div>
      </div>
      ${ov.summary ? `<p style="margin:4px 0 0; font-size:0.88rem; color:var(--text);">${esc(ov.summary)}</p>` : ""}
      ${bullets}
    </section>
  `;
  if (HAS_MANUSCRIPT) {
    document.getElementById("mode-manuscript").style.display = "inline-block";
    document.getElementById("level1-mode-group").style.display = "flex";
    document.getElementById("mode-manuscript").classList.toggle("active", dagMode === "manuscript");
    document.getElementById("mode-chapters").classList.toggle("active", dagMode === "chapters");
    document.getElementById("mode-pillars").classList.toggle("active", dagMode === "pillars");
  }
  window.__renderAllMath(el);
}

function setDagMode(mode) {
  dagMode = mode;
  const msBtn = document.getElementById("mode-manuscript");
  if (msBtn) msBtn.classList.toggle("active", mode === "manuscript");
  document.getElementById("mode-chapters").classList.toggle("active", mode === "chapters");
  document.getElementById("mode-pillars").classList.toggle("active", mode === "pillars");
  resetDag();
}

function setLevel1Mode(mode) {
  level1Mode = mode;
  document.getElementById("l1-manuscript").classList.toggle("active", mode === "manuscript");
  document.getElementById("l1-clusters").classList.toggle("active", mode === "clusters");
  renderChapters();
}

function applyDagTransform() {
  const vp = document.getElementById("dag-viewport");
  vp.setAttribute("transform", `translate(${dagTx}, ${dagTy}) scale(${dagScale})`);
}

function zoomDag(factor) {
  dagScale = Math.max(0.25, Math.min(3.0, dagScale * factor));
  applyDagTransform();
}

function resetDag() {
  dagScale = 1.0;
  dagTx = 24;
  dagTy = 24;
  renderDag();
}

function computeLayeredLayout(nodes, edges) {
  const idSet = new Set(nodes.map(n => n.id));
  const preds = new Map(nodes.map(n => [n.id, []]));
  const succs = new Map(nodes.map(n => [n.id, []]));
  for (const e of edges) {
    if (idSet.has(e.from) && idSet.has(e.to) && e.from !== e.to) {
      preds.get(e.to).push(e.from);
      succs.get(e.from).push(e.to);
    }
  }
  const layer = new Map();
  const indeg = new Map(nodes.map(n => [n.id, preds.get(n.id).length]));
  const q = nodes.filter(n => indeg.get(n.id) === 0).map(n => n.id);
  for (const id of q) layer.set(id, 0);

  let head = 0;
  while (head < q.length) {
    const u = q[head++];
    const lu = layer.get(u) || 0;
    for (const v of succs.get(u)) {
      layer.set(v, Math.max(layer.get(v) || 0, lu + 1));
      indeg.set(v, indeg.get(v) - 1);
      if (indeg.get(v) === 0) q.push(v);
    }
  }
  // Assign fallback layers for any cycle nodes or disconnected nodes
  nodes.forEach((n, idx) => {
    if (!layer.has(n.id)) layer.set(n.id, Math.floor(idx / 5));
  });

  const byLayer = new Map();
  for (const n of nodes) {
    const l = layer.get(n.id);
    if (!byLayer.has(l)) byLayer.set(l, []);
    byLayer.get(l).push(n);
  }
  const colW = 240;
  const rowH = 88;
  const pos = new Map();
  const sortedLayers = Array.from(byLayer.keys()).sort((a, b) => a - b);
  sortedLayers.forEach((l, colIdx) => {
    const bucket = byLayer.get(l);
    bucket.forEach((n, rowIdx) => {
      pos.set(n.id, { x: colIdx * colW + 20, y: rowIdx * rowH + 20, w: 205, h: 62 });
    });
  });
  return pos;
}

function renderDag() {
  const vp = document.getElementById("dag-viewport");
  const tooltip = document.getElementById("dag-tooltip");

  let nodes = [];
  let edges = [];
  if (dagMode === "manuscript" && HAS_MANUSCRIPT) {
    nodes = PROOF_DATA.manuscript_chapters.map(c => ({
      id: c.id,
      title: `Ch. ${c.id}: ${c.title}`,
      meta: `${fmtNum(c.word_count)} words · ${c.unique_links_count} anchors`,
      tooltip: `<strong>Ch. ${c.id}: ${esc(c.title)}</strong><br/>${fmtNum(c.word_count)} words · ${c.unique_links_count} verified \\leanlink anchors${c.page_no ? " · manuscript.pdf p. " + c.page_no : ""}`,
      isRoot: c.id === 1,
      onClick: () => {
        activeManuscriptChapterId = c.id;
        level1Mode = "manuscript";
        switchLevel(1);
      }
    }));
    edges = PROOF_DATA.manuscript_edges || [];
  } else if (dagMode === "chapters") {
    nodes = PROOF_DATA.chapters.map(c => ({
      id: c.id,
      title: c.title,
      meta: `${fmtNum(c.decl_count)} decls · ${fmtNum(c.total_loc)} LOC`,
      tooltip: `<strong>${esc(c.title)}</strong><br/>${fmtNum(c.decl_count)} declarations, ${fmtNum(c.total_loc)} LOC${c.idioms.length ? "<br/>Idioms: " + esc(c.idioms.join(", ")) : ""}`,
      isRoot: false,
      onClick: () => {
        activeChapterFilterId = c.id;
        switchLevel(1);
      }
    }));
    edges = PROOF_DATA.chapter_edges;
  } else {
    nodes = PROOF_DATA.pillar_ids.map(id => DECL_BY_ID.get(id)).filter(Boolean).map(d => ({
      id: d.id,
      title: d.display_title,
      meta: `score ${d.bottleneck_score} · ${fmtNum(d.body_loc)} LOC`,
      tooltip: `<strong>${esc(d.name)}</strong><br/>Kind: ${esc(d.kind)} · Bottleneck: ${d.bottleneck_score} · In/Out: ${d.in_degree}/${d.out_degree}<br/>Module: ${esc(d.module_path)}`,
      isRoot: d.is_root,
      onClick: () => {
        selectedDeclId = d.id;
        switchLevel(2);
      }
    }));
    edges = PROOF_DATA.pillar_edges;
  }

  const pos = computeLayeredLayout(nodes, edges);
  const edgeSvg = edges.map(e => {
    const a = pos.get(e.from);
    const b = pos.get(e.to);
    if (!a || !b) return "";
    const x1 = a.x + a.w;
    const y1 = a.y + a.h / 2;
    const x2 = b.x;
    const y2 = b.y + b.h / 2;
    const mx = (x1 + x2) / 2;
    return `<path class="dag-edge" d="M ${x1} ${y1} C ${mx} ${y1}, ${mx} ${y2}, ${x2} ${y2}" marker-end="url(#arrow)" />`;
  }).join("");

  const nodeSvg = nodes.map(n => {
    const p = pos.get(n.id);
    const shortTitle = n.title.length > 26 ? n.title.slice(0, 24) + "…" : n.title;
    return `
      <g class="dag-node ${n.isRoot ? "root" : ""}" data-node-id="${esc(n.id)}" transform="translate(${p.x},${p.y})" style="cursor:pointer;">
        <rect width="${p.w}" height="${p.h}" />
        <text class="node-title" x="10" y="25">${esc(shortTitle)}</text>
        <text class="node-meta" x="10" y="45">${esc(n.meta)}</text>
      </g>`;
  }).join("");

  vp.innerHTML = edgeSvg + nodeSvg;
  applyDagTransform();

  const nodeMap = new Map(nodes.map(n => [String(n.id), n]));
  vp.querySelectorAll(".dag-node").forEach(el => {
    const nodeObj = nodeMap.get(el.getAttribute("data-node-id"));
    if (!nodeObj) return;
    el.addEventListener("click", () => nodeObj.onClick());
    el.addEventListener("mousemove", ev => {
      const box = document.querySelector(".dag-shell").getBoundingClientRect();
      tooltip.style.display = "block";
      tooltip.style.left = Math.min(box.width - 330, ev.clientX - box.left + 14) + "px";
      tooltip.style.top = Math.max(10, ev.clientY - box.top + 14) + "px";
      tooltip.innerHTML = nodeObj.tooltip;
    });
    el.addEventListener("mouseleave", () => { tooltip.style.display = "none"; });
  });
}

// Pan & wheel zoom on SVG
(function initDagPanZoom() {
  const svg = document.getElementById("dag-svg");
  let dragging = false;
  let sx = 0, sy = 0;
  svg.addEventListener("mousedown", e => {
    if (e.target.closest(".dag-node")) return;
    dragging = true;
    sx = e.clientX - dagTx;
    sy = e.clientY - dagTy;
  });
  window.addEventListener("mousemove", e => {
    if (!dragging) return;
    dagTx = e.clientX - sx;
    dagTy = e.clientY - sy;
    applyDagTransform();
  });
  window.addEventListener("mouseup", () => { dragging = false; });
  svg.addEventListener("wheel", e => {
    e.preventDefault();
    zoomDag(e.deltaY < 0 ? 1.09 : 0.92);
  }, { passive: false });
})();

function clearChapterFilter() {
  activeChapterFilterId = null;
  activeManuscriptChapterId = null;
  document.getElementById("chapter-filter").value = "";
  renderChapters();
}

function renderManuscriptChapters(grid, q) {
  const filtered = PROOF_DATA.manuscript_chapters.filter(c => {
    if (activeManuscriptChapterId !== null && c.id !== activeManuscriptChapterId) return false;
    if (!q) return true;
    return c.title.toLowerCase().includes(q)
      || c.summary.toLowerCase().includes(q)
      || c.subsections.some(s => s.toLowerCase().includes(q));
  });
  if (!filtered.length) {
    grid.innerHTML = `<div class="chapter-card" style="color:var(--muted);">No matching manuscript chapters.</div>`;
    return;
  }
  grid.innerHTML = filtered.map(c => {
    const subsHtml = c.subsections.map(s => `<span class="subsec-pill">${esc(s)}</span>`).join("");
    const thmByName = new Map((c.theorem_entries || []).map(t => [t.name, t]));
    const declsHtml = c.decl_ids.map(id => DECL_BY_ID.get(id)).filter(Boolean).map(d => {
      const te = thmByName.get(d.name);
      const heading = (te && te.title) ? te.title : d.display_title;
      const kind = (te && te.kind) ? te.kind : d.kind;
      const auditBadge = d.audit_status === "verified"
        ? `<span class="badge verified">verified</span>`
        : (d.audit_status === "issue" ? `<span class="badge issue">audit flag</span>` : "");
      return `
        <div class="stmt-item">
          <div class="stmt-head">
            <span class="badge">${esc(kind)}</span>
            <strong>${esc(heading)}</strong>
            ${auditBadge}
            <button class="stmt-link" onclick="inspectDecl(${d.id})">${esc(d.name)}</button>
          </div>
          <div class="math-box">\\[${d.latex_stmt}\\]</div>
        </div>`;
    }).join("");
    const extraChips = c.all_link_ids
      .filter(id => !c.decl_ids.includes(id))
      .slice(0, 24)
      .map(id => DECL_BY_ID.get(id))
      .filter(Boolean)
      .map(d => `<button class="dep-chip" onclick="inspectDecl(${d.id})">${esc(d.name)}</button>`)
      .join("");
    return `
      <article class="chapter-card">
        <div class="chapter-head">
          <div>
            <h2 class="chapter-title">Chapter ${c.id}. ${esc(c.title)}</h2>
            <div style="margin-top:6px; display:flex; flex-wrap:wrap; gap:6px;">
              ${c.pdf_href ? `<a class="ext-link" href="${esc(c.pdf_href)}" target="_blank">Read in manuscript.pdf${c.page_no ? ` (p. ${c.page_no})` : ""}</a>` : ""}
              <a class="ext-link" href="${esc(c.tex_href)}" target="_blank">${esc(c.filename)}</a>
            </div>
          </div>
          <div>
            <span class="badge">${fmtNum(c.word_count)} words</span>
            <span class="badge verified">${c.unique_links_count} verified \\leanlinks</span>
            <span class="badge">${c.theorem_entries.length} statements</span>
          </div>
        </div>
        <p style="font-size:0.9rem; margin:4px 0 8px;">${esc(c.summary)}</p>
        ${subsHtml ? `<div class="subsec-list">${subsHtml}</div>` : ""}
        ${declsHtml}
        ${extraChips ? `<details class="iface-box"><summary>All Anchored Lean Constants in Chapter ${c.id} (${c.all_link_ids.length})</summary><div style="margin-top:8px;">${extraChips}</div></details>` : ""}
      </article>`;
  }).join("");
  window.__renderAllMath(grid);
}

function renderChapters() {
  const q = (document.getElementById("chapter-filter").value || "").toLowerCase().trim();
  const grid = document.getElementById("chapter-grid");
  if (HAS_MANUSCRIPT && level1Mode === "manuscript") {
    document.getElementById("l1-manuscript").classList.add("active");
    document.getElementById("l1-clusters").classList.remove("active");
    renderManuscriptChapters(grid, q);
    return;
  }
  if (HAS_MANUSCRIPT) {
    document.getElementById("l1-manuscript").classList.remove("active");
    document.getElementById("l1-clusters").classList.add("active");
  }
  const filtered = PROOF_DATA.chapters.filter(c => {
    if (activeChapterFilterId !== null && c.id !== activeChapterFilterId) return false;
    if (!q) return true;
    return c.title.toLowerCase().includes(q) || c.idioms.some(i => i.toLowerCase().includes(q));
  });

  if (!filtered.length) {
    grid.innerHTML = `<div class="chapter-card" style="color:var(--muted);">No matching chapters.</div>`;
    return;
  }

  grid.innerHTML = filtered.map((c, idx) => {
    const idiomBadges = c.idioms.map(i => `<span class="badge idiom">${esc(i)}</span>`).join("");
    const inList = c.interface_in.map(it => `<li><code>${esc(it.name)}</code> (${esc(it.kind)})</li>`).join("") || "<li style='color:var(--muted)'>Standard library / self-contained</li>";
    const outList = c.interface_out.map(it => `<li><code>${esc(it.name)}</code> (${esc(it.kind)})</li>`).join("") || "<li style='color:var(--muted)'>Internal / terminal chapter</li>";
    const declsHtml = c.decl_ids.map(id => DECL_BY_ID.get(id)).filter(Boolean).map(d => {
      const auditBadge = d.audit_status === "verified"
        ? `<span class="badge verified">verified</span>`
        : (d.audit_status === "issue" ? `<span class="badge issue">audit flag</span>` : "");
      return `
        <div class="stmt-item">
          <div class="stmt-head">
            <span class="badge">${esc(d.kind)}</span>
            <strong>${esc(d.display_title)}</strong>
            ${auditBadge}
            <button class="stmt-link" onclick="inspectDecl(${d.id})">${esc(d.name)}</button>
          </div>
          <div class="math-box">\\[${d.latex_stmt}\\]</div>
        </div>`;
    }).join("");

    return `
      <article class="chapter-card">
        <div class="chapter-head">
          <div>
            <h2 class="chapter-title">${idx + 1}. ${esc(c.title)}</h2>
            <div style="margin-top:4px;">${idiomBadges}</div>
          </div>
          <div>
            <span class="badge">${fmtNum(c.decl_count)} decls</span>
            <span class="badge">${fmtNum(c.total_loc)} LOC</span>
          </div>
        </div>
        <details class="iface-box">
          <summary>Formal Interface (Inputs ⊢ Outputs)</summary>
          <div class="iface-cols">
            <div><strong>Inputs (${c.interface_in.length})</strong><ul>${inList}</ul></div>
            <div><strong>Outputs (${c.interface_out.length})</strong><ul>${outList}</ul></div>
          </div>
        </details>
        ${declsHtml}
      </article>`;
  }).join("");

  window.__renderAllMath(grid);
}

function inspectDecl(id) {
  selectedDeclId = id;
  switchLevel(2);
}

function inspectDeclByName(name) {
  const d = DECL_BY_NAME.get(name);
  if (d) inspectDecl(d.id);
}

function renderDeclList() {
  const q = (document.getElementById("decl-search").value || "").toLowerCase().trim();
  const listEl = document.getElementById("decl-list");
  const items = PROOF_DATA.declarations.filter(d => {
    if (!q) return true;
    return d.name.toLowerCase().includes(q)
      || d.module_path.toLowerCase().includes(q)
      || d.kind.toLowerCase().includes(q);
  }).sort((a, b) => (b.bottleneck_score - a.bottleneck_score) || (b.body_loc - a.body_loc));

  listEl.innerHTML = items.slice(0, 250).map(d => `
    <button class="decl-row ${d.id === selectedDeclId ? "selected" : ""}" onclick="selectDecl(${d.id})">
      <div class="nm">${esc(d.name)}</div>
      <div class="sub">${esc(d.kind)} · score ${d.bottleneck_score} · ${fmtNum(d.body_loc)} LOC</div>
    </button>
  `).join("");
}

function selectDecl(id) {
  selectedDeclId = id;
  renderDeclList();
  renderDeclDetail(id);
}

function renderDeclDetail(id) {
  const panel = document.getElementById("decl-detail");
  const d = DECL_BY_ID.get(id);
  if (!d) {
    panel.innerHTML = `<p style="color:var(--muted);">No declaration selected.</p>`;
    return;
  }
  const axiomsHtml = d.axioms.length
    ? d.axioms.map(a => `<span class="badge">${esc(a)}</span>`).join("")
    : `<span class="badge">axioms not recorded</span>`;
  const auditBadge = d.audit_status === "verified"
    ? `<span class="badge verified">audit verified</span>`
    : (d.audit_status === "issue"
      ? `<span class="badge issue">audit issue: ${esc(d.audit_notes.join("; "))}</span>`
      : `<span class="badge">audit unchecked</span>`);

  const depsHtml = d.deps.length
    ? d.deps.map(dep => `<button class="dep-chip" onclick="inspectDeclByName('${esc(dep.name)}')">${esc(dep.name)}</button>`).join("")
    : `<span style="color:var(--muted); font-size:0.84rem;">No recorded project dependencies</span>`;

  const revHtml = d.dependents.length
    ? d.dependents.map(dep => `<button class="dep-chip" onclick="inspectDeclByName('${esc(dep.name)}')">${esc(dep.name)}</button>`).join("")
    : `<span style="color:var(--muted); font-size:0.84rem;">Terminal / root declaration</span>`;

  panel.innerHTML = `
    <div style="margin-bottom:10px;">
      <span class="badge">${esc(d.kind)}</span>
      ${d.is_root ? '<span class="badge root">root theorem</span>' : ""}
      ${auditBadge}
      <span class="badge">bottleneck ${d.bottleneck_score}</span>
      <span class="badge">${fmtNum(d.body_loc)} LOC</span>
    </div>
    <h2 style="margin:0 0 6px; font-family:var(--mono); font-size:1rem; word-break:break-all;">${esc(d.name)}</h2>
    <div style="color:var(--muted); font-size:0.82rem; margin-bottom:12px;">
      Module: <code>${esc(d.module_path || "unknown")}</code>
      ${d.start_line ? ` (lines ${d.start_line}–${d.end_line || d.start_line})` : ""}
      · In-degree: ${d.in_degree} · Out-degree: ${d.out_degree}
    </div>
    ${d.docstring ? `<p style="font-size:0.9rem;">${esc(d.docstring)}</p>` : ""}
    <h3 style="font-size:0.86rem; color:var(--muted); margin:12px 0 4px;">Mathematical Statement</h3>
    <div class="math-box">\\[${d.latex_stmt}\\]</div>
    <h3 style="font-size:0.86rem; color:var(--muted); margin:12px 0 4px;">Exact Lean 4 Type Signature</h3>
    <pre class="lean-code">${esc(d.type_sig || "(not recorded)")}</pre>
    <h3 style="font-size:0.86rem; color:var(--muted); margin:12px 0 4px;">Axiom Footprint</h3>
    <div>${axiomsHtml}</div>
    <h3 style="font-size:0.86rem; color:var(--muted); margin:12px 0 4px;">Upstream Dependencies (${d.deps.length})</h3>
    <div>${depsHtml}</div>
    <h3 style="font-size:0.86rem; color:var(--muted); margin:12px 0 4px;">Downstream Dependents (${d.dependents.length})</h3>
    <div>${revHtml}</div>
  `;
  window.__renderAllMath(panel);
}

renderMetrics();
renderOverview();
renderDag();
</script>
</body>
</html>
"""


def generate_blueprint(
    db: DbHandle,
    output_path: str | Path | None = None,
    *,
    title: str | None = None,
    audit_report: dict[str, Any] | None = None,
    max_pillars: int = 30,
    max_chapters: int = 24,
    chapters_dir: str | Path | None = None,
    manuscript_href: str | None = None,
    readers_guide_href: str | None = None,
    overview: dict[str, Any] | None = None,
    chapter_page_map: dict[int, int] | None = None,
) -> str:
    """Generate a self-contained, zero-build interactive HTML blueprint (`blueprint.html`)."""
    with open_db(db, readonly=False) as conn:
        payload = _build_blueprint_payload(
            conn,
            title=title,
            audit_report=audit_report,
            max_pillars=max_pillars,
            max_chapters=max_chapters,
            chapters_dir=chapters_dir,
            manuscript_href=manuscript_href,
            readers_guide_href=readers_guide_href,
            overview=overview,
            chapter_page_map=chapter_page_map,
        )

    safe_title = html.escape(payload["title"])
    rendered = _BLUEPRINT_TEMPLATE.replace("__TITLE__", safe_title).replace(
        "__PROOF_DATA_JSON__", _safe_json_for_script(payload)
    )

    if output_path is not None:
        out = Path(output_path)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(rendered, encoding="utf-8")
    return rendered
