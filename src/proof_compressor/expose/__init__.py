"""Stage 3 mathematical exposition, symbol registry, blueprint, and fidelity auditor."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from proof_compressor.expose._db import DbHandle, open_db
from proof_compressor.expose.audit import audit_latex, format_audit_markdown
from proof_compressor.expose.blueprint import generate_blueprint
from proof_compressor.expose.filter import (
    BookkeepingClassification,
    classify_bookkeeping,
    detect_bookkeeping_leaks,
    extract_all_cluster_idioms,
    extract_proof_idioms,
    tag_bookkeeping,
)
from proof_compressor.expose.latex import generate_latex
from proof_compressor.expose.symbols import (
    SymbolEntry,
    SymbolRegistry,
    build_symbol_registry,
    lean_type_to_latex,
)


def expose_all(
    db: DbHandle,
    output_dir: str | Path,
    *,
    title: str | None = None,
    max_symbols: int = 120,
    max_bottlenecks: int = 25,
    max_pillars: int = 30,
    update_bookkeeping: bool = True,
) -> dict[str, Any]:
    """Run the full Stage 3 exposition pipeline: filter -> symbols -> latex -> audit -> blueprint."""
    out_dir = Path(output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    paper_path = out_dir / "paper.tex"
    blueprint_path = out_dir / "blueprint.html"
    audit_json_path = out_dir / "audit_report.json"
    audit_md_path = out_dir / "audit_report.md"

    with open_db(db, readonly=False) as conn:
        bk_stats = tag_bookkeeping(conn, update_db=update_bookkeeping)
        registry = build_symbol_registry(conn, max_symbols=max_symbols)
        latex_text = generate_latex(
            conn,
            output_path=paper_path,
            title=title,
            max_bottlenecks=max_bottlenecks,
        )
        audit_report = audit_latex(
            conn,
            latex_text,
            output_json=audit_json_path,
            output_md=audit_md_path,
        )
        generate_blueprint(
            conn,
            output_path=blueprint_path,
            title=title,
            audit_report=audit_report,
            max_pillars=max_pillars,
        )

    return {
        "paper_path": str(paper_path),
        "blueprint_path": str(blueprint_path),
        "audit_json_path": str(audit_json_path),
        "audit_md_path": str(audit_md_path),
        "symbols_registered": len(registry.entries),
        "bookkeeping": bk_stats,
        "audit_passed": bool(audit_report["passed"]),
        "fidelity_score": float(audit_report["fidelity_score"]),
        "audit_summary": audit_report["summary"],
    }


__all__ = [
    "BookkeepingClassification",
    "SymbolEntry",
    "SymbolRegistry",
    "audit_latex",
    "build_symbol_registry",
    "classify_bookkeeping",
    "detect_bookkeeping_leaks",
    "expose_all",
    "extract_all_cluster_idioms",
    "extract_proof_idioms",
    "format_audit_markdown",
    "generate_blueprint",
    "generate_latex",
    "lean_type_to_latex",
    "tag_bookkeeping",
]
