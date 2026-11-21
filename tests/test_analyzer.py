"""Comprehensive tests for proof_compressor.analyze and proof_compressor.cli."""

from __future__ import annotations

import json
import sqlite3
import time
from pathlib import Path

import pytest

from proof_compressor.analyze import (
    analyze_dedup,
    analyze_topology,
    cluster_graph,
    prune_reachability,
    run_analysis,
)
from proof_compressor.analyze.topology import (
    build_csr,
    compute_dag_flow,
    compute_dominators_chk,
    tarjan_scc_iterative,
    transitive_reduction,
)
from proof_compressor.cli import main as cli_main
from proof_compressor.schema import (
    batch_insert_declarations,
    batch_insert_edges,
    batch_insert_module_imports,
    batch_insert_modules,
    connect_db,
    init_db,
)

from conftest import build_synthetic_dag_db


# ---------------------------------------------------------------------------
# Reachability pruning tests
# ---------------------------------------------------------------------------


def test_prune_reachability_exact_and_mathlib_boundary(tmp_path: Path) -> None:
    db_path = tmp_path / "prune.db"
    conn, info = build_synthetic_dag_db(
        db_path, num_pillars=4, leaves_per_pillar=15, dead_nodes=60, include_cycle=True
    )
    try:
        stats = prune_reachability(conn, roots=[info["root"]])
        assert stats.root_names == ["Main.RH"]
        assert stats.fallback_used is False
        assert stats.dead_modules == 1
        assert stats.dead_project_declarations == 60
        assert stats.reachable_project_declarations == 1 + 4 * (2 + 15) + 3
        assert stats.module_elimination_pct > 0
        assert stats.loc_elimination_pct > 0

        # Mathlib boundary recorded, but Mathlib internal helper NOT expanded
        assert stats.mathlib_boundary_declarations == 1
        rows = {
            r["name"]: r["reachable"]
            for r in conn.execute(
                """
                SELECT d.name, m.reachable
                FROM declarations d
                JOIN metrics m ON m.decl_id = d.id
                """
            ).fetchall()
        }
        assert rows[info["mathlib_boundary"]] == 1
        assert rows[info["mathlib_internal"]] == 0
        for dead in info["dead"]:
            assert rows[dead] == 0
        for pillar in info["pillars"]:
            assert rows[pillar] == 1
    finally:
        conn.close()


def test_prune_auto_detect_roots_and_module_fallback(tmp_path: Path) -> None:
    db_path = tmp_path / "fallback.db"
    conn = init_db(db_path)
    try:
        batch_insert_modules(
            conn,
            [
                ("Main", "Main", 10, 0),
                ("Core.Helper", "Core", 100, 0),
                ("Unused.Dead", "Unused", 500, 0),
            ],
        )
        conn.commit()
        mids = {r["path"]: r["id"] for r in conn.execute("SELECT id, path FROM modules")}
        batch_insert_declarations(
            conn,
            [
                ("Main.RH", "RH", mids["Main"], "theorem", "True", "h1", 5, 0, "", 0, 0, 1, 5, None),
                ("Core.Helper.step1", "step1", mids["Core.Helper"], "theorem", "True", "h2", 40, 0, "", 0, 0, 1, 40, None),
                ("Unused.Dead.junk", "junk", mids["Unused.Dead"], "theorem", "True", "h3", 200, 0, "", 0, 0, 1, 200, None),
            ],
        )
        batch_insert_module_imports(
            conn,
            [(mids["Main"], "Core.Helper", mids["Core.Helper"])],
        )
        conn.commit()

        # No declaration edges exist, so auto-detect + module-import fallback should recover Core.Helper
        stats = prune_reachability(conn, roots=None, use_module_import_fallback=True)
        assert stats.root_names == ["Main.RH"]
        assert stats.fallback_used is True
        assert stats.reachable_modules == 2
        assert stats.dead_modules == 1
        assert stats.reachable_project_declarations == 2
        assert stats.dead_project_declarations == 1
    finally:
        conn.close()


# ---------------------------------------------------------------------------
# Deduplication tests
# ---------------------------------------------------------------------------


def test_dedup_exact_near_isomorphic_and_mathlib(tmp_path: Path) -> None:
    db_path = tmp_path / "dedup.db"
    conn, info = build_synthetic_dag_db(
        db_path, num_pillars=4, leaves_per_pillar=10, dead_nodes=20, include_duplicates=True
    )
    try:
        prune_reachability(conn, roots=[info["root"]])
        report = analyze_dedup(conn, reachable_only=True)

        # Two shared duplicate hashes (j == 1, j == 2) across 4 pillars => 2 groups, 6 redundant decls
        assert report.exact_duplicate_group_count >= 2
        assert report.exact_duplicate_redundant_decls >= 6
        assert report.exact_duplicate_reducible_loc > 0
        assert report.estimated_post_dedup_loc <= report.analyzed_loc
        assert report.estimated_post_dedup_loc == max(
            0, report.analyzed_loc - report.total_estimated_reducible_loc
        )
        assert report.mathlib_absorption_candidates >= 1
    finally:
        conn.close()


# ---------------------------------------------------------------------------
# Topology: Tarjan SCC, CHK dominators, bottleneck scoring, 3000+ node DAG
# ---------------------------------------------------------------------------


def test_topology_scc_dominators_and_bottlenecks(tmp_path: Path) -> None:
    db_path = tmp_path / "topo.db"
    conn, info = build_synthetic_dag_db(
        db_path, num_pillars=5, leaves_per_pillar=20, dead_nodes=50, include_cycle=True
    )
    try:
        prune_reachability(conn, roots=[info["root"]])
        topo = analyze_topology(conn, top_k=10, reachable_only=True)

        assert topo.nontrivial_scc_count == 1
        assert topo.largest_scc_size == 3
        assert topo.exact_flow_mode is True
        assert topo.max_dominator_depth >= 2

        # All 3 cycle nodes must share the exact same scc_id
        scc_rows = {
            r["name"]: r["scc_id"]
            for r in conn.execute(
                """
                SELECT d.name, m.scc_id
                FROM declarations d
                JOIN metrics m ON m.decl_id = d.id
                WHERE d.name LIKE '%.mutual_rec_%'
                """
            ).fetchall()
        }
        assert len(scc_rows) == 3
        assert len(set(scc_rows.values())) == 1

        # Top bottlenecks must include pillars and Main.RH, NOT bookkeeping helpers
        top_names = [b["name"] for b in topo.top_bottlenecks]
        assert "Main.RH" in top_names
        pillar_hits = [p for p in info["pillars"] if p in top_names]
        assert len(pillar_hits) >= 4
        assert not any("cast_nonneg_aux" in nm for nm in top_names)

        # High-centrality defs should pick up our core operators
        def_names = [d["name"] for d in topo.top_definitions]
        assert len(def_names) >= 5
        for dn in info["defs"]:
            assert dn in def_names

        # Backbone DAG should be transitively reduced (no redundant shortcut edges)
        assert len(topo.backbone_edges) >= 1
    finally:
        conn.close()


def test_topology_scales_on_3200_node_dag_sketch_mode(tmp_path: Path) -> None:
    """Stress-test iterative Tarjan, CHK dominators, landmark sketch flow, and clustering on 3,200+ nodes."""
    db_path = tmp_path / "large_dag.db"
    conn, info = build_synthetic_dag_db(
        db_path,
        num_pillars=8,
        leaves_per_pillar=400,  # 8 * 402 + 1 = 3,217 reachable project nodes
        dead_nodes=500,
        include_cycle=True,
    )
    try:
        t0 = time.perf_counter()
        prune_stats = prune_reachability(conn, roots=[info["root"]])
        topo = analyze_topology(
            conn,
            top_k=15,
            reachable_only=True,
            exact_flow_threshold=2500,  # forces landmark sketch mode
        )
        cl = cluster_graph(conn, max_chapters=8, max_sections=32)
        elapsed = time.perf_counter() - t0

        assert prune_stats.reachable_project_declarations > 3200
        assert prune_stats.dead_project_declarations == 500
        assert topo.node_count > 3200
        assert topo.exact_flow_mode is False
        assert topo.nontrivial_scc_count == 1
        assert elapsed < 10.0, f"3200-node pipeline too slow: {elapsed:.2f}s"

        # Pillars must still rise to the top in landmark sketch mode
        top_names = {b["name"] for b in topo.top_bottlenecks}
        assert len(top_names & set(info["pillars"])) >= 5

        assert 1 <= cl.chapter_count <= 8
        assert cl.section_count >= cl.chapter_count
    finally:
        conn.close()


def test_deep_chain_no_recursion_error() -> None:
    """Verify iterative Tarjan and CHK dominators handle a 2,500-deep chain without RecursionError."""
    n = 2500
    edges = [(i, i + 1) for i in range(n - 1)]
    out_off, out_tgt, in_off, in_tgt = build_csr(n, edges)
    scc_id, num_sccs = tarjan_scc_iterative(n, out_off, out_tgt)
    assert num_sccs == n
    # Reverse topological property: scc(u) > scc(v) for edge u -> v
    for u, v in edges:
        assert scc_id[u] > scc_id[v]

    from array import array

    loc = array("I", [10]) * n
    idom, dom_depth, dom_count, dom_loc = compute_dominators_chk(
        n, [0], out_off, out_tgt, in_off, in_tgt, loc
    )
    assert dom_depth[0] == 1
    assert dom_depth[n - 1] == n
    assert dom_count[0] == n
    assert dom_loc[0] == n * 10
    assert idom[1] == 0

    # Transitive reduction on a 4-chain with all shortcuts keeps only 3 edges
    reach = {0: {1, 2, 3}, 1: {2, 3}, 2: {3}, 3: set()}
    assert transitive_reduction([0, 1, 2, 3], reach) == [(0, 1), (1, 2), (2, 3)]


# ---------------------------------------------------------------------------
# Clustering tests
# ---------------------------------------------------------------------------


def test_cluster_hierarchy_and_formal_interfaces(tmp_path: Path) -> None:
    db_path = tmp_path / "cluster.db"
    conn, info = build_synthetic_dag_db(
        db_path, num_pillars=5, leaves_per_pillar=12, dead_nodes=30
    )
    try:
        res = run_analysis(conn, roots=[info["root"]], max_chapters=6, max_sections=20)
        cl_stats = res["cluster"]
        assert cl_stats["chapter_count"] >= 2
        assert cl_stats["section_count"] >= cl_stats["chapter_count"]
        assert 0.0 <= cl_stats["internal_edge_ratio"] <= 1.0

        chapters = conn.execute(
            "SELECT * FROM clusters WHERE level = 0 ORDER BY id"
        ).fetchall()
        sections = conn.execute(
            "SELECT * FROM clusters WHERE level = 1 ORDER BY id"
        ).fetchall()
        assert len(chapters) == cl_stats["chapter_count"]
        assert len(sections) == cl_stats["section_count"]

        chap_ids = {c["id"] for c in chapters}
        sec_ids = {s["id"] for s in sections}
        for s in sections:
            assert s["parent_id"] in chap_ids
            assert isinstance(json.loads(s["interface_in_json"]), list)
            assert isinstance(json.loads(s["interface_out_json"]), list)

        # Every reachable project declaration must point to a valid level-1 section
        unassigned = conn.execute(
            """
            SELECT COUNT(*) FROM metrics m
            JOIN declarations d ON d.id = m.decl_id
            WHERE m.reachable = 1 AND d.is_mathlib = 0 AND m.cluster_id IS NULL
            """
        ).fetchone()[0]
        assert unassigned == 0

        assigned_cids = {
            r[0]
            for r in conn.execute(
                "SELECT DISTINCT cluster_id FROM metrics WHERE cluster_id IS NOT NULL"
            ).fetchall()
        }
        assert assigned_cids.issubset(sec_ids)
    finally:
        conn.close()


# ---------------------------------------------------------------------------
# CLI tests (including progress callback contract check!)
# ---------------------------------------------------------------------------


def test_cli_end_to_end_subcommands(
    sample_multipart_tar_gz: list[Path], tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    db = tmp_path / "cli_demo.db"
    out_dir = tmp_path / "out"
    part01 = sample_multipart_tar_gz[0]

    assert cli_main(["ingest", str(part01), "--db", str(db), "--json"]) == 0
    ing_out = json.loads(capsys.readouterr().out)
    assert ing_out["files_ingested"] == 6

    assert cli_main(["analyze", str(db), "--roots", "RH_demo", "--json"]) == 0
    an_out = json.loads(capsys.readouterr().out)
    assert an_out["prune"]["reachable_project_declarations"] >= 4
    assert an_out["prune"]["dead_modules"] == 1

    assert cli_main(["stats", str(db), "--json"]) == 0
    st_out = json.loads(capsys.readouterr().out)
    assert st_out["summary"]["project_modules"] == 6

    assert cli_main(["bottlenecks", str(db), "--top-k", "5", "--include-defs", "--json"]) == 0
    bn_out = json.loads(capsys.readouterr().out)
    assert len(bn_out["bottlenecks"]) >= 2

    assert cli_main(["expose", str(db), "--out", str(out_dir), "--json"]) == 0
    ex_out = json.loads(capsys.readouterr().out)
    assert Path(ex_out["paper_tex"]).exists()
    assert Path(ex_out["blueprint_html"]).exists()
    assert Path(ex_out["audit_json"]).exists()

    assert (
        cli_main(
            [
                "audit",
                str(db),
                "--latex",
                str(out_dir / "paper.tex"),
                "--json",
            ]
        )
        == 0
    )
    aud_out = json.loads(capsys.readouterr().out)
    assert aud_out["summary"]["unknown_leanlinks"] == 0
    assert aud_out["summary"]["unreachable_leanlinks"] == 0

    assert cli_main(["refactor-plan", str(db), "--min-loc", "1", "--json"]) == 0
    ref_out = json.loads(capsys.readouterr().out)
    assert ref_out["work_order_count"] >= 1

    # Full run-all pipeline
    db2 = tmp_path / "cli_runall.db"
    out2 = tmp_path / "out_runall"
    assert (
        cli_main(
            [
                "run-all",
                str(part01),
                "--db",
                str(db2),
                "--out",
                str(out2),
                "--roots",
                "RH_demo",
                "--json",
            ]
        )
        == 0
    )
    ra_out = json.loads(capsys.readouterr().out)
    assert Path(ra_out["artifacts"]["paper_tex"]).exists()
    assert Path(ra_out["artifacts"]["blueprint_html"]).exists()


def test_cli_ingest_progress_callback_contract(
    sample_tar_gz: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Regression test: cli.py progress_cb must accept the dict payload emitted by stream_archive."""
    import proof_compressor.ingest.stream_archive as sa

    orig_ingest = sa.ingest_source

    def _wrapped(*args, **kwargs):
        kwargs["progress_every"] = 1  # Force progress_cb invocation even on tiny archive
        return orig_ingest(*args, **kwargs)

    monkeypatch.setattr(sa, "ingest_source", _wrapped)

    db = tmp_path / "prog.db"
    # Non-quiet, non-json mode activates progress_cb
    rc = cli_main(["ingest", str(sample_tar_gz), "--db", str(db)])
    assert rc == 0
