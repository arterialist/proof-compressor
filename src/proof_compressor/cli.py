"""Unified CLI (`proof-compressor`) wiring ingest, analyze, expose, audit, and refactor stages."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, Sequence

from proof_compressor.analyze import (
    analyze_topology,
    run_analysis,
)
from proof_compressor.schema import connect_db, get_db_summary, get_meta


def _parse_roots(raw_roots: Sequence[str] | None) -> list[str] | None:
    if not raw_roots:
        return None
    out: list[str] = []
    for item in raw_roots:
        for part in item.split(","):
            p = part.strip()
            if p:
                out.append(p)
    return out or None


def _resolve_db_arg(args: argparse.Namespace) -> Path:
    db_val = getattr(args, "db", None) or getattr(args, "db_pos", None)
    if not db_val:
        raise SystemExit("error: database path required (pass --db PATH or positional PATH)")
    return Path(db_val)


def _json_load_meta(conn: Any, key: str) -> Any:
    raw = get_meta(conn, key)
    if not raw:
        return None
    try:
        return json.loads(raw)
    except Exception:
        return None


def _print_json(data: Any) -> None:
    print(json.dumps(data, indent=2, default=str))


def _registry_count(registry: Any) -> int:
    if hasattr(registry, "entries"):
        return len(registry.entries)
    if hasattr(registry, "symbols"):
        return len(registry.symbols)
    try:
        return len(registry)
    except TypeError:
        return 0


def _make_ingest_progress_cb(prefix: str) -> Any:
    def _progress(info: dict[str, Any]) -> None:
        phase = info.get("phase", "")
        elapsed = float(info.get("elapsed_s", 0.0))
        if phase == "pass1":
            files = int(info.get("files_ingested", 0))
            decls = int(info.get("declarations", 0))
            print(
                f"[{prefix} pass1] {files:,} files, {decls:,} decls ({elapsed:.1f}s)",
                file=sys.stderr,
                flush=True,
            )
        elif phase == "pass2":
            mods = int(info.get("modules_resolved", 0))
            edges = int(info.get("edges", info.get("edges_inserted", 0)))
            print(
                f"[{prefix} pass2] {mods:,} modules resolved, {edges:,} edges ({elapsed:.1f}s)",
                file=sys.stderr,
                flush=True,
            )
        else:
            print(f"[{prefix}] {info}", file=sys.stderr, flush=True)

    return _progress


def _cmd_ingest(args: argparse.Namespace) -> int:
    from proof_compressor.ingest.stream_archive import ingest_source

    db_path = Path(args.db)
    t0 = time.perf_counter()

    progress_cb = None if (args.quiet or args.json) else _make_ingest_progress_cb("ingest")

    stats = ingest_source(
        args.source,
        db_path,
        max_files=args.max_files,
        path_filter=args.path_filter,
        include_mathlib=args.include_mathlib,
        strip_prefixes=tuple(args.strip_prefix or ()),
        batch_size=args.batch_size,
        progress_cb=progress_cb,
    )
    elapsed = round(time.perf_counter() - t0, 2)
    payload = stats.to_dict() if hasattr(stats, "to_dict") else dict(stats)
    payload["elapsed_s"] = elapsed
    payload["db"] = str(db_path)

    if args.json:
        _print_json(payload)
    else:
        print(f"Ingested {args.source} -> {db_path} in {elapsed:.2f}s")
        for k, v in payload.items():
            if k not in ("elapsed_s", "db"):
                print(f"  {k}: {v}")
    return 0


def _cmd_ingest_olean(args: argparse.Namespace) -> int:
    from proof_compressor.ingest.olean_bridge import ingest_olean_jsonl

    db_path = Path(args.db)
    t0 = time.perf_counter()
    stats = ingest_olean_jsonl(
        args.jsonl,
        db_path,
        merge=not args.no_merge,
        overwrite_types=args.overwrite_types,
        create_boundary_stubs=not args.no_boundary_stubs,
        batch_size=args.batch_size,
    )
    elapsed = round(time.perf_counter() - t0, 2)
    payload = stats.to_dict() if hasattr(stats, "to_dict") else dict(stats)
    payload["elapsed_s"] = elapsed
    payload["db"] = str(db_path)

    if args.json:
        _print_json(payload)
    else:
        print(f"Ingested .olean JSONL {args.jsonl} -> {db_path} in {elapsed:.2f}s")
        for k, v in payload.items():
            if k not in ("elapsed_s", "db"):
                print(f"  {k}: {v}")
    return 0


def _cmd_analyze(args: argparse.Namespace) -> int:
    db_path = _resolve_db_arg(args)
    roots = _parse_roots(args.roots)
    t0 = time.perf_counter()

    result = run_analysis(
        db_path,
        roots=roots,
        top_k=args.top_k,
        max_chapters=args.chapters,
        max_sections=args.sections,
        use_module_import_fallback=not args.no_module_fallback,
        similarity_threshold=args.similarity,
    )
    elapsed = round(time.perf_counter() - t0, 2)
    result["elapsed_s"] = elapsed

    if args.json:
        _print_json(result)
        return 0

    pr = result["prune"]
    dd = result["dedup"]
    tp = result["topology"]
    cl = result["cluster"]

    print(f"Analysis complete on {db_path} in {elapsed:.2f}s")
    print(f"  Roots ({len(pr['root_names'])}): {', '.join(pr['root_names'][:8])}")
    print(
        f"  Modules:      {pr['raw_modules']:,} raw -> {pr['reachable_modules']:,} reachable "
        f"({pr['module_elimination_pct']:.1f}% eliminated)"
    )
    print(
        f"  Project LOC:  {pr['raw_project_loc']:,} raw -> {pr['reachable_project_loc']:,} reachable "
        f"({pr['loc_elimination_pct']:.1f}% eliminated)"
    )
    print(
        f"  Declarations: {pr['raw_project_declarations']:,} raw -> "
        f"{pr['reachable_project_declarations']:,} reachable "
        f"({pr['declaration_elimination_pct']:.1f}% eliminated)"
    )
    print(
        f"  Mathlib bdry: {pr['mathlib_boundary_declarations']:,} decls across "
        f"{pr['mathlib_boundary_modules']:,} modules"
    )
    print(
        f"  Dedup/Absorb: {dd['exact_duplicate_group_count']:,} exact groups, "
        f"{dd['near_duplicate_group_count']:,} near groups, "
        f"{dd['mathlib_absorption_candidates']:,} Mathlib candidates "
        f"(est. -{dd['total_estimated_reducible_loc']:,} LOC / -{dd['dedup_reduction_pct']:.1f}%)"
    )
    print(
        f"  Topology:     {tp['node_count']:,} nodes, {tp['edge_count']:,} edges, "
        f"{tp['scc_count']:,} SCCs ({tp['nontrivial_scc_count']} cycles), "
        f"max dom depth {tp['max_dominator_depth']}"
    )
    print(
        f"  Clusters:     {cl['chapter_count']} chapters, {cl['section_count']} sections "
        f"(internal edge ratio {cl['internal_edge_ratio'] * 100:.1f}%)"
    )
    return 0


def _cmd_stats(args: argparse.Namespace) -> int:
    db_path = _resolve_db_arg(args)
    conn = connect_db(db_path, readonly=True)
    try:
        summary = get_db_summary(conn)
        prune_stats = _json_load_meta(conn, "analysis_prune_stats")
        dedup_stats = _json_load_meta(conn, "analysis_dedup_stats")
        topo_stats = _json_load_meta(conn, "analysis_topology_stats")
        cluster_stats = _json_load_meta(conn, "analysis_cluster_stats")
        roots = _json_load_meta(conn, "analysis_roots")

        payload = {
            "db": str(db_path),
            "summary": summary,
            "roots": roots,
            "prune": prune_stats,
            "dedup": dedup_stats,
            "topology": {
                k: v
                for k, v in (topo_stats or {}).items()
                if k not in ("top_bottlenecks", "top_definitions", "backbone_nodes", "backbone_edges")
            }
            if topo_stats
            else None,
            "cluster": cluster_stats,
        }

        if args.json:
            _print_json(payload)
            return 0

        print(f"=== proof-compressor stats: {db_path} ===")
        print(
            f"Raw DB: {summary['project_modules']:,} project modules "
            f"({summary['total_loc']:,} LOC), "
            f"{summary['project_declarations']:,} project decls, "
            f"{summary['edges']:,} edges, {summary['module_imports']:,} module imports"
        )
        if prune_stats:
            print("\n[Reachability Pruning]")
            print(f"  Roots: {', '.join(prune_stats.get('root_names', [])[:10])}")
            print(
                f"  Modules:      {prune_stats['raw_modules']:,} -> "
                f"{prune_stats['reachable_modules']:,} "
                f"(-{prune_stats['dead_modules']:,}, {prune_stats['module_elimination_pct']:.1f}%)"
            )
            print(
                f"  Project LOC:  {prune_stats['raw_project_loc']:,} -> "
                f"{prune_stats['reachable_project_loc']:,} "
                f"(-{prune_stats['dead_project_loc']:,}, {prune_stats['loc_elimination_pct']:.1f}%)"
            )
            print(
                f"  Declarations: {prune_stats['raw_project_declarations']:,} -> "
                f"{prune_stats['reachable_project_declarations']:,} "
                f"(-{prune_stats['dead_project_declarations']:,}, "
                f"{prune_stats['declaration_elimination_pct']:.1f}%)"
            )
            print(
                f"  Mathlib bdry: {prune_stats['mathlib_boundary_declarations']:,} decls / "
                f"{prune_stats['mathlib_boundary_modules']:,} modules"
            )
            if prune_stats.get("top_dead_packages"):
                print("  Top dead packages:")
                for pkg in prune_stats["top_dead_packages"][:5]:
                    print(
                        f"    - {pkg['package']}: {pkg['dead_modules']:,} dead mods "
                        f"({pkg['dead_loc']:,} LOC)"
                    )

        if dedup_stats:
            print("\n[Deduplication & Mathlib Absorption]")
            print(
                f"  Exact duplicate groups: {dedup_stats['exact_duplicate_group_count']:,} "
                f"({dedup_stats['exact_duplicate_redundant_decls']:,} decls, "
                f"{dedup_stats['exact_duplicate_reducible_loc']:,} LOC)"
            )
            print(
                f"  Near-duplicate groups:  {dedup_stats['near_duplicate_group_count']:,} "
                f"({dedup_stats['near_duplicate_redundant_decls']:,} decls, "
                f"{dedup_stats['near_duplicate_reducible_loc']:,} LOC)"
            )
            print(
                f"  Isomorphic def groups:  {dedup_stats['isomorphic_def_group_count']:,}"
            )
            print(
                f"  Mathlib candidates:     {dedup_stats['mathlib_absorption_candidates']:,} "
                f"({dedup_stats['mathlib_absorption_loc']:,} LOC)"
            )
            print(
                f"  Est. post-dedup LOC:    {dedup_stats['estimated_post_dedup_loc']:,} "
                f"(-{dedup_stats['dedup_reduction_pct']:.1f}%)"
            )

        if cluster_stats and cluster_stats.get("chapters"):
            print(
                f"\n[Modular Chapters ({cluster_stats['chapter_count']} chapters, "
                f"{cluster_stats['section_count']} sections, "
                f"{cluster_stats['internal_edge_ratio'] * 100:.1f}% internal edges)]"
            )
            for idx, ch in enumerate(cluster_stats["chapters"], start=1):
                print(
                    f"  Ch {idx:2d}. {ch['title']} — {ch['decl_count']:,} decls, "
                    f"{ch['total_loc']:,} LOC "
                    f"(in:{ch['interface_in_count']} / out:{ch['interface_out_count']})"
                )
        return 0
    finally:
        conn.close()


def _cmd_bottlenecks(args: argparse.Namespace) -> int:
    db_path = _resolve_db_arg(args)
    conn = connect_db(db_path, readonly=True)
    try:
        topo = _json_load_meta(conn, "analysis_topology_stats")
        bottlenecks: list[dict[str, Any]] = []
        definitions: list[dict[str, Any]] = []

        if topo and len(topo.get("top_bottlenecks", [])) >= args.top_k:
            bottlenecks = topo["top_bottlenecks"][: args.top_k]
            definitions = topo.get("top_definitions", [])[: args.top_k]
        else:
            # Query directly from metrics + declarations
            rows = conn.execute(
                "SELECT d.id, d.name, d.short_name, d.kind, COALESCE(mo.path, '') AS module, "
                "d.body_loc, m.in_degree, m.out_degree, m.scc_id, m.dominator_depth, "
                "m.bottleneck_score, SUBSTR(COALESCE(d.type_sig, ''), 1, 200) AS sig "
                "FROM metrics m "
                "JOIN declarations d ON d.id = m.decl_id "
                "LEFT JOIN modules mo ON mo.id = d.module_id "
                "WHERE m.reachable = 1 AND d.is_mathlib = 0 AND d.is_bookkeeping = 0 "
                "AND d.kind IN ('theorem', 'lemma') "
                "ORDER BY m.bottleneck_score DESC LIMIT ?",
                (args.top_k,),
            ).fetchall()
            for r in rows:
                bottlenecks.append(
                    {
                        "decl_id": r["id"],
                        "name": r["name"],
                        "short_name": r["short_name"],
                        "kind": r["kind"],
                        "module": r["module"],
                        "body_loc": r["body_loc"],
                        "in_degree": r["in_degree"],
                        "out_degree": r["out_degree"],
                        "scc_id": r["scc_id"],
                        "dominator_depth": r["dominator_depth"],
                        "bottleneck_score": r["bottleneck_score"],
                        "type_sig_preview": r["sig"],
                    }
                )
            if args.include_defs:
                drows = conn.execute(
                    "SELECT d.id, d.name, d.short_name, d.kind, COALESCE(mo.path, '') AS module, "
                    "d.body_loc, m.in_degree, m.out_degree, m.dominator_depth, m.bottleneck_score, "
                    "SUBSTR(COALESCE(d.type_sig, ''), 1, 200) AS sig "
                    "FROM metrics m "
                    "JOIN declarations d ON d.id = m.decl_id "
                    "LEFT JOIN modules mo ON mo.id = d.module_id "
                    "WHERE m.reachable = 1 AND d.is_mathlib = 0 AND d.is_bookkeeping = 0 "
                    "AND d.kind IN ('def', 'abbrev', 'structure', 'class', 'inductive') "
                    "ORDER BY m.in_degree DESC, m.bottleneck_score DESC LIMIT ?",
                    (args.top_k,),
                ).fetchall()
                for r in drows:
                    definitions.append(dict(r))

        payload: dict[str, Any] = {"bottlenecks": bottlenecks}
        if args.include_defs:
            payload["definitions"] = definitions

        if args.json:
            _print_json(payload)
            return 0

        print(f"Top {len(bottlenecks)} Mathematical Bottleneck Theorems ({db_path}):")
        for idx, b in enumerate(bottlenecks, start=1):
            dom_loc = b.get("dominated_loc")
            desc_loc = b.get("descendant_loc")
            extra = ""
            if dom_loc is not None and desc_loc is not None:
                extra = f" | domLOC={dom_loc:,} descLOC={desc_loc:,}"
            print(
                f"  {idx:2d}. [{b['bottleneck_score']:.3f}] {b['name']} "
                f"({b['kind']}, in={b['in_degree']}, out={b['out_degree']}, "
                f"depth={b['dominator_depth']}{extra})"
            )
            if b.get("module"):
                print(f"      module: {b['module']}")
            if b.get("type_sig_preview"):
                sig = " ".join(b["type_sig_preview"].split())
                print(f"      type:   {sig[:120]}")

        if args.include_defs and definitions:
            print(f"\nTop {len(definitions)} High-Centrality Definitions:")
            for idx, d in enumerate(definitions, start=1):
                cent = d.get("centrality", d.get("bottleneck_score", 0.0))
                print(
                    f"  {idx:2d}. [{cent:.3f}] {d['name']} "
                    f"({d['kind']}, in={d['in_degree']}, module={d.get('module', '')})"
                )
        return 0
    finally:
        conn.close()


def _cmd_expose(args: argparse.Namespace) -> int:
    db_path = _resolve_db_arg(args)
    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.perf_counter()

    from proof_compressor.expose.audit import audit_latex
    from proof_compressor.expose.blueprint import generate_blueprint
    from proof_compressor.expose.filter import tag_bookkeeping
    from proof_compressor.expose.latex import generate_latex
    from proof_compressor.expose.symbols import build_symbol_registry

    bk_stats = None
    if not args.no_bookkeeping_tag:
        bk_stats = tag_bookkeeping(db_path, update_db=True)

    registry = build_symbol_registry(
        db_path,
        max_symbols=args.max_symbols,
        reachable_only=True,
    )

    tex_path = out_dir / "paper.tex"
    latex_src = generate_latex(
        db_path,
        output_path=tex_path,
        title=args.title,
        max_bottlenecks=args.max_bottlenecks,
        max_theorems_per_cluster=args.max_theorems_per_cluster,
    )

    audit_json = out_dir / "audit_report.json"
    audit_md = out_dir / "audit_report.md"
    audit_report = audit_latex(
        db_path,
        latex_src,
        output_json=audit_json,
        output_md=audit_md,
    )

    html_path = out_dir / "blueprint.html"
    generate_blueprint(
        db_path,
        output_path=html_path,
        title=args.title,
        audit_report=audit_report,
        max_pillars=args.max_pillars,
    )

    elapsed = round(time.perf_counter() - t0, 2)
    sym_count = _registry_count(registry)
    payload = {
        "db": str(db_path),
        "output_dir": str(out_dir),
        "paper_tex": str(tex_path),
        "blueprint_html": str(html_path),
        "audit_json": str(audit_json),
        "audit_md": str(audit_md),
        "symbols_registered": sym_count,
        "bookkeeping_tagging": bk_stats,
        "audit_summary": audit_report.get("summary", audit_report),
        "elapsed_s": elapsed,
    }

    if args.json:
        _print_json(payload)
    else:
        print(f"Exposition generated in {out_dir} ({elapsed:.2f}s)")
        print(f"  Symbols:   {sym_count}")
        print(f"  LaTeX:     {tex_path}")
        print(f"  Blueprint: {html_path}")
        print(f"  Audit:     {audit_json} / {audit_md}")
    return 0


def _cmd_audit(args: argparse.Namespace) -> int:
    from proof_compressor.expose.audit import audit_latex, format_audit_markdown

    db_path = _resolve_db_arg(args)
    latex_path = Path(args.latex)
    latex_src = latex_path.read_text(encoding="utf-8")

    report = audit_latex(
        db_path,
        latex_src,
        output_json=Path(args.out_json) if args.out_json else None,
        output_md=Path(args.out_md) if args.out_md else None,
        bottleneck_threshold=args.bottleneck_threshold,
    )

    if args.json:
        _print_json(report)
    else:
        print(format_audit_markdown(report))

    if args.strict:
        passed = report.get("passed", report.get("ok", True))
        if not passed:
            return 2
    return 0


def _cmd_refactor_plan(args: argparse.Namespace) -> int:
    from proof_compressor.refactor.planner import (
        format_refactor_plan_markdown,
        plan_refactors,
    )

    db_path = _resolve_db_arg(args)
    out_json = Path(args.out) if args.out else None
    work_orders = plan_refactors(
        db_path,
        top_k=args.top_k,
        min_loc=args.min_loc,
        output_path=out_json,
    )

    md_text = format_refactor_plan_markdown(work_orders)
    if args.out_md:
        out_md = Path(args.out_md)
        out_md.parent.mkdir(parents=True, exist_ok=True)
        out_md.write_text(md_text, encoding="utf-8")

    gate_dict = None
    if args.verify_project:
        from proof_compressor.refactor.gate import verify_refactor_gate

        gate_res = verify_refactor_gate(
            Path(args.verify_project),
            run_lake=not args.no_lake,
        )
        gate_dict = (
            gate_res.to_dict()
            if hasattr(gate_res, "to_dict")
            else vars(gate_res)
        )

    payload: dict[str, Any] = {
        "work_order_count": len(work_orders),
        "work_orders": work_orders,
    }
    if gate_dict is not None:
        payload["gate"] = gate_dict

    if args.json:
        _print_json(payload)
    else:
        print(md_text)
        if gate_dict is not None:
            print("\n[Verification Gate]")
            print(json.dumps(gate_dict, indent=2, default=str))
    return 0


def _cmd_run_all(args: argparse.Namespace) -> int:
    t_total = time.perf_counter()
    db_path = Path(args.db)
    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    roots = _parse_roots(args.roots)

    summary: dict[str, Any] = {
        "source": str(args.source) if args.source else None,
        "db": str(db_path),
        "output_dir": str(out_dir),
        "timings_s": {},
    }

    # Stage 1: Ingest
    if not args.skip_ingest:
        if not args.source:
            raise SystemExit("error: source path required unless --skip-ingest is set")
        from proof_compressor.ingest.stream_archive import ingest_source

        t0 = time.perf_counter()
        progress_cb = (
            None if (args.quiet or args.json) else _make_ingest_progress_cb("1/5 ingest")
        )

        istats = ingest_source(
            args.source,
            db_path,
            max_files=args.max_files,
            path_filter=args.path_filter,
            include_mathlib=args.include_mathlib,
            progress_cb=progress_cb,
        )
        summary["ingest"] = istats.to_dict() if hasattr(istats, "to_dict") else dict(istats)
        summary["timings_s"]["ingest"] = round(time.perf_counter() - t0, 2)

    # Stage 2: Analyze
    t0 = time.perf_counter()
    analysis = run_analysis(
        db_path,
        roots=roots,
        top_k=args.top_k,
        max_chapters=args.chapters,
        max_sections=args.sections,
        use_module_import_fallback=not args.no_module_fallback,
    )
    summary["analysis"] = {
        "prune": analysis["prune"],
        "dedup": {
            k: v
            for k, v in analysis["dedup"].items()
            if not k.startswith("top_")
        },
        "topology": {
            k: v
            for k, v in analysis["topology"].items()
            if k not in ("backbone_nodes", "backbone_edges")
        },
        "cluster": {
            "chapter_count": analysis["cluster"]["chapter_count"],
            "section_count": analysis["cluster"]["section_count"],
            "internal_edge_ratio": analysis["cluster"]["internal_edge_ratio"],
        },
    }
    summary["timings_s"]["analyze"] = round(time.perf_counter() - t0, 2)

    # Stage 3 & 4: Expose + Audit
    from proof_compressor.expose.audit import audit_latex
    from proof_compressor.expose.blueprint import generate_blueprint
    from proof_compressor.expose.filter import tag_bookkeeping
    from proof_compressor.expose.latex import generate_latex
    from proof_compressor.expose.symbols import build_symbol_registry
    from proof_compressor.refactor.planner import (
        format_refactor_plan_markdown,
        plan_refactors,
    )

    t0 = time.perf_counter()
    tag_bookkeeping(db_path, update_db=True)
    registry = build_symbol_registry(db_path, max_symbols=args.max_symbols, reachable_only=True)
    tex_path = out_dir / "paper.tex"
    latex_src = generate_latex(
        db_path,
        output_path=tex_path,
        title=args.title,
        max_bottlenecks=args.top_k,
    )
    summary["timings_s"]["expose_latex"] = round(time.perf_counter() - t0, 2)

    t0 = time.perf_counter()
    audit_json = out_dir / "audit_report.json"
    audit_md = out_dir / "audit_report.md"
    audit_report = audit_latex(
        db_path,
        latex_src,
        output_json=audit_json,
        output_md=audit_md,
    )
    summary["timings_s"]["audit"] = round(time.perf_counter() - t0, 2)

    t0 = time.perf_counter()
    html_path = out_dir / "blueprint.html"
    generate_blueprint(
        db_path,
        output_path=html_path,
        title=args.title,
        audit_report=audit_report,
        max_pillars=max(args.top_k, 30),
    )
    summary["timings_s"]["blueprint"] = round(time.perf_counter() - t0, 2)

    # Stage 5: Refactor plan
    t0 = time.perf_counter()
    ref_json = out_dir / "refactor_plan.json"
    ref_md = out_dir / "refactor_plan.md"
    work_orders = plan_refactors(
        db_path,
        top_k=args.refactor_top_k,
        min_loc=args.refactor_min_loc,
        output_path=ref_json,
    )
    ref_md.write_text(format_refactor_plan_markdown(work_orders), encoding="utf-8")
    summary["timings_s"]["refactor_plan"] = round(time.perf_counter() - t0, 2)

    summary["timings_s"]["total"] = round(time.perf_counter() - t_total, 2)
    summary["artifacts"] = {
        "paper_tex": str(tex_path),
        "blueprint_html": str(html_path),
        "audit_json": str(audit_json),
        "audit_md": str(audit_md),
        "refactor_plan_json": str(ref_json),
        "refactor_plan_md": str(ref_md),
    }
    summary["symbols_registered"] = _registry_count(registry)
    summary["refactor_work_orders"] = len(work_orders)
    summary["audit_summary"] = audit_report.get("summary", audit_report)

    summary_path = out_dir / "pipeline_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, default=str), encoding="utf-8")

    if args.json:
        _print_json(summary)
    else:
        pr = analysis["prune"]
        print(f"=== proof-compressor run-all complete ({summary['timings_s']['total']:.2f}s) ===")
        print(
            f"  Reachability: {pr['raw_modules']:,} -> {pr['reachable_modules']:,} modules "
            f"(-{pr['module_elimination_pct']:.1f}%), "
            f"{pr['raw_project_loc']:,} -> {pr['reachable_project_loc']:,} LOC "
            f"(-{pr['loc_elimination_pct']:.1f}%)"
        )
        print(f"  Bottlenecks:  {len(analysis['topology']['top_bottlenecks'])} pillars extracted")
        print(
            f"  Chapters:     {analysis['cluster']['chapter_count']} chapters / "
            f"{analysis['cluster']['section_count']} sections"
        )
        print(f"  Outputs:      {out_dir}")
        print(f"    - {tex_path}")
        print(f"    - {html_path}")
        print(f"    - {audit_json}")
        print(f"    - {ref_json}")
        print(f"    - {summary_path}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="proof-compressor",
        description="Compress, analyze, and expose massive Lean 4 proof repositories.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    # ingest
    p_ing = sub.add_parser("ingest", help="Stream Lean 4 source files or .tar.gz parts into SQLite.")
    p_ing.add_argument("source", help="Directory, .tar.gz, .tar.gz.part01, or glob pattern.")
    p_ing.add_argument("--db", required=True, help="Output SQLite database path.")
    p_ing.add_argument("--max-files", type=int, default=None, help="Limit number of .lean files ingested.")
    p_ing.add_argument("--filter", dest="path_filter", default=None, help="Substring filter on file paths.")
    p_ing.add_argument("--include-mathlib", action="store_true", help="Include Mathlib files if present.")
    p_ing.add_argument("--strip-prefix", action="append", default=None, help="Path prefix to strip.")
    p_ing.add_argument("--batch-size", type=int, default=5000, help="SQLite batch insert size.")
    p_ing.add_argument("--quiet", action="store_true", help="Suppress progress output.")
    p_ing.add_argument("--json", action="store_true", help="Emit JSON output.")
    p_ing.set_defaults(func=_cmd_ingest)

    # ingest-olean
    p_ol = sub.add_parser("ingest-olean", help="Import JSONL emitted by lean_extractor into SQLite.")
    p_ol.add_argument("jsonl", help="Path to JSONL file emitted by ExtractDag.")
    p_ol.add_argument("--db", required=True, help="Target SQLite database path.")
    p_ol.add_argument("--no-merge", action="store_true", help="Replace existing DB content instead of merging.")
    p_ol.add_argument("--overwrite-types", action="store_true", help="Overwrite existing type signatures.")
    p_ol.add_argument("--no-boundary-stubs", action="store_true", help="Do not create stub rows for Mathlib boundary.")
    p_ol.add_argument("--batch-size", type=int, default=5000, help="SQLite batch insert size.")
    p_ol.add_argument("--json", action="store_true", help="Emit JSON output.")
    p_ol.set_defaults(func=_cmd_ingest_olean)

    # analyze
    p_an = sub.add_parser("analyze", help="Run pruning, deduplication, topology, and clustering.")
    p_an.add_argument("db_pos", nargs="?", default=None, help="SQLite DB path (or use --db).")
    p_an.add_argument("--db", default=None, help="SQLite database path.")
    p_an.add_argument(
        "--roots",
        action="append",
        default=None,
        help="Root theorem name(s) or file(s), comma-separated or repeatable. Auto-detected if omitted.",
    )
    p_an.add_argument("--top-k", type=int, default=25, help="Number of top bottleneck theorems to extract.")
    p_an.add_argument("--chapters", type=int, default=12, help="Maximum top-level chapters.")
    p_an.add_argument("--sections", type=int, default=96, help="Maximum level-1 sections.")
    p_an.add_argument(
        "--no-module-fallback",
        action="store_true",
        help="Disable module-import fallback when declaration edges are missing.",
    )
    p_an.add_argument("--similarity", type=float, default=0.85, help="Near-duplicate Jaccard threshold.")
    p_an.add_argument("--json", action="store_true", help="Emit JSON output.")
    p_an.set_defaults(func=_cmd_analyze)

    # stats
    p_st = sub.add_parser("stats", help="Display compression, dedup, and chapter statistics.")
    p_st.add_argument("db_pos", nargs="?", default=None, help="SQLite DB path (or use --db).")
    p_st.add_argument("--db", default=None, help="SQLite database path.")
    p_st.add_argument("--json", action="store_true", help="Emit JSON output.")
    p_st.set_defaults(func=_cmd_stats)

    # bottlenecks
    p_bn = sub.add_parser("bottlenecks", help="List top mathematical bottleneck theorems and definitions.")
    p_bn.add_argument("db_pos", nargs="?", default=None, help="SQLite DB path (or use --db).")
    p_bn.add_argument("--db", default=None, help="SQLite database path.")
    p_bn.add_argument("--top-k", type=int, default=25, help="Number of bottlenecks to display.")
    p_bn.add_argument("--include-defs", action="store_true", help="Also list high-centrality definitions.")
    p_bn.add_argument("--json", action="store_true", help="Emit JSON output.")
    p_bn.set_defaults(func=_cmd_bottlenecks)

    # expose
    p_ex = sub.add_parser("expose", help="Generate symbol registry, paper.tex, audit report, and blueprint.html.")
    p_ex.add_argument("db_pos", nargs="?", default=None, help="SQLite DB path (or use --db).")
    p_ex.add_argument("--db", default=None, help="SQLite database path.")
    p_ex.add_argument("--out", required=True, help="Output directory for generated artifacts.")
    p_ex.add_argument("--title", default=None, help="Custom manuscript/blueprint title.")
    p_ex.add_argument("--max-symbols", type=int, default=120, help="Maximum symbols in symbol registry.")
    p_ex.add_argument("--max-bottlenecks", type=int, default=25, help="Maximum bottleneck theorems in overview.")
    p_ex.add_argument("--max-theorems-per-cluster", type=int, default=12, help="Max theorems per chapter.")
    p_ex.add_argument("--max-pillars", type=int, default=30, help="Maximum pillars in blueprint DAG.")
    p_ex.add_argument("--no-bookkeeping-tag", action="store_true", help="Skip re-tagging bookkeeping lemmas.")
    p_ex.add_argument("--json", action="store_true", help="Emit JSON output.")
    p_ex.set_defaults(func=_cmd_expose)

    # audit
    p_au = sub.add_parser("audit", help="Audit generated LaTeX manuscript against the Lean SQLite graph.")
    p_au.add_argument("db_pos", nargs="?", default=None, help="SQLite DB path (or use --db).")
    p_au.add_argument("--db", default=None, help="SQLite database path.")
    p_au.add_argument("--latex", required=True, help="Path to generated paper.tex.")
    p_au.add_argument("--out-json", default=None, help="Optional path to write audit_report.json.")
    p_au.add_argument("--out-md", default=None, help="Optional path to write audit_report.md.")
    p_au.add_argument("--bottleneck-threshold", type=float, default=None, help="Min bottleneck score for omission alerts.")
    p_au.add_argument("--strict", action="store_true", help="Exit with code 2 if audit detects failures.")
    p_au.add_argument("--json", action="store_true", help="Emit JSON output.")
    p_au.set_defaults(func=_cmd_audit)

    # refactor-plan
    p_rf = sub.add_parser("refactor-plan", help="Generate Stage 4 kernel-checked refactoring work orders.")
    p_rf.add_argument("db_pos", nargs="?", default=None, help="SQLite DB path (or use --db).")
    p_rf.add_argument("--db", default=None, help="SQLite database path.")
    p_rf.add_argument("--out", default=None, help="Optional path to write refactor_plan.json.")
    p_rf.add_argument("--out-md", default=None, help="Optional path to write refactor_plan.md.")
    p_rf.add_argument("--top-k", type=int, default=20, help="Number of refactoring targets to emit.")
    p_rf.add_argument("--min-loc", type=int, default=30, help="Minimum internal LOC per target.")
    p_rf.add_argument("--verify-project", default=None, help="Optional Lean project dir to run verification gate on.")
    p_rf.add_argument("--no-lake", action="store_true", help="Skip lake build when running verification gate.")
    p_rf.add_argument("--json", action="store_true", help="Emit JSON output.")
    p_rf.set_defaults(func=_cmd_refactor_plan)

    # run-all
    p_all = sub.add_parser("run-all", help="Run full pipeline: ingest -> analyze -> expose -> audit -> refactor-plan.")
    p_all.add_argument("source", nargs="?", default=None, help="Source dir, .tar.gz, or .part01/glob.")
    p_all.add_argument("--db", required=True, help="SQLite database path.")
    p_all.add_argument("--out", required=True, help="Output directory for all generated artifacts.")
    p_all.add_argument("--skip-ingest", action="store_true", help="Skip ingestion and reuse existing DB.")
    p_all.add_argument("--roots", action="append", default=None, help="Root theorem name(s), comma-separated or repeatable.")
    p_all.add_argument("--max-files", type=int, default=None, help="Limit number of .lean files ingested.")
    p_all.add_argument("--filter", dest="path_filter", default=None, help="Substring filter during ingestion.")
    p_all.add_argument("--include-mathlib", action="store_true", help="Include Mathlib files during ingestion.")
    p_all.add_argument("--top-k", type=int, default=25, help="Top-K bottleneck theorems.")
    p_all.add_argument("--chapters", type=int, default=12, help="Maximum top-level chapters.")
    p_all.add_argument("--sections", type=int, default=96, help="Maximum level-1 sections.")
    p_all.add_argument("--no-module-fallback", action="store_true", help="Disable module-import fallback.")
    p_all.add_argument("--max-symbols", type=int, default=120, help="Maximum registered symbols.")
    p_all.add_argument("--title", default=None, help="Custom manuscript/blueprint title.")
    p_all.add_argument("--refactor-top-k", type=int, default=20, help="Number of refactor work orders.")
    p_all.add_argument("--refactor-min-loc", type=int, default=30, help="Minimum LOC for refactor targets.")
    p_all.add_argument("--quiet", action="store_true", help="Suppress progress logs.")
    p_all.add_argument("--json", action="store_true", help="Emit JSON summary.")
    p_all.set_defaults(func=_cmd_run_all)

    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
