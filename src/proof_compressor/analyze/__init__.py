"""Stage 2 analysis pipeline: pruning, deduplication, topology/bottlenecks, and clustering."""

from __future__ import annotations

import sqlite3
from pathlib import Path
from typing import Any, Sequence

from proof_compressor.analyze.cluster import ClusterReport, cluster_graph
from proof_compressor.analyze.dedup import DedupReport, analyze_dedup, normalize_signature
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
    "resolve_roots",
    "prune_reachability",
    "analyze_dedup",
    "normalize_signature",
    "analyze_topology",
    "tarjan_scc_iterative",
    "compute_dominators_chk",
    "transitive_reduction",
    "cluster_graph",
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
