"""Stage 2 analysis pipeline: pruning, deduplication, topology/bottlenecks, and clustering."""

from __future__ import annotations

import sqlite3
from pathlib import Path
from typing import Any, Sequence

from proof_compressor.analyze.cluster import ClusterReport, cluster_graph
from proof_compressor.analyze.consolidate import (
    ConsolidationOp,
    ConsolidationPlan,
    ConsolidationReport,
    apply_consolidations_to_lines,
    plan_consolidation,
    verify_consolidation_plan_with_sources,
)
from proof_compressor.analyze.dedup import DedupReport, analyze_dedup, normalize_signature
from proof_compressor.analyze.materialize import (
    VALID_MATERIALIZE_MODES,
    MaterializeReport,
    PrunePlan,
    TransformResult,
    compute_prune_plan,
    is_pure_import_barrel_source,
    materialize_project,
    strip_lean_comments,
    transform_lean_source,
    transform_lean_source_full,
)
from proof_compressor.analyze.merge_modules import (
    MergeReport,
    MergeUnit,
    merge_project_modules,
    parse_lakefile_lib_globs,
)
from proof_compressor.analyze.prune import PruneStats, prune_reachability, resolve_roots
from proof_compressor.analyze.topology import (
    TopologyReport,
    analyze_topology,
    compute_dominators_chk,
    tarjan_scc_iterative,
    transitive_reduction,
)
from proof_compressor.schema import connect_db

__all__ = [
    "PruneStats",
    "DedupReport",
    "TopologyReport",
    "ClusterReport",
    "ConsolidationOp",
    "ConsolidationPlan",
    "ConsolidationReport",
    "PrunePlan",
    "TransformResult",
    "MaterializeReport",
    "MergeUnit",
    "MergeReport",
    "VALID_MATERIALIZE_MODES",
    "resolve_roots",
    "prune_reachability",
    "analyze_dedup",
    "normalize_signature",
    "analyze_topology",
    "tarjan_scc_iterative",
    "compute_dominators_chk",
    "transitive_reduction",
    "cluster_graph",
    "plan_consolidation",
    "verify_consolidation_plan_with_sources",
    "apply_consolidations_to_lines",
    "compute_prune_plan",
    "strip_lean_comments",
    "is_pure_import_barrel_source",
    "transform_lean_source",
    "transform_lean_source_full",
    "materialize_project",
    "merge_project_modules",
    "parse_lakefile_lib_globs",
    "run_analysis",
]


def run_analysis(
    db: sqlite3.Connection | str | Path,
    *,
    roots: Sequence[str] | None = None,
    top_k: int = 25,
    max_chapters: int = 12,
    max_sections: int = 96,
    use_module_import_fallback: bool = True,
    similarity_threshold: float = 0.85,
) -> dict[str, Any]:
    """Run the full analysis pipeline (prune -> dedup -> topology -> cluster) on a DB."""
    should_close = False
    if isinstance(db, sqlite3.Connection):
        conn = db
    else:
        conn = connect_db(db)
        should_close = True

    try:
        prune_stats = prune_reachability(
            conn,
            roots=roots,
            use_module_import_fallback=use_module_import_fallback,
        )
        dedup_report = analyze_dedup(
            conn,
            reachable_only=True,
            similarity_threshold=similarity_threshold,
        )
        topology_report = analyze_topology(
            conn,
            top_k=top_k,
            reachable_only=True,
        )
        cluster_report = cluster_graph(
            conn,
            max_chapters=max_chapters,
            max_sections=max_sections,
            reachable_only=True,
        )
        return {
            "prune": prune_stats.to_dict(),
            "dedup": dedup_report.to_dict(),
            "topology": topology_report.to_dict(),
            "cluster": cluster_report.to_dict(),
        }
    finally:
        if should_close:
            conn.close()
