"""Stage 4 kernel-checked refactoring planner and verification gate."""

from __future__ import annotations

from proof_compressor.refactor.gate import (
    STANDARD_LEAN_AXIOMS,
    GateResult,
    count_effective_loc,
    count_files_effective_loc,
    find_lake_binary,
    parse_check_signatures,
    parse_print_axioms,
    verify_refactor_gate,
)
from proof_compressor.refactor.planner import (
    RefactorWorkOrder,
    format_refactor_plan_markdown,
    plan_refactors,
)

__all__ = [
    "GateResult",
    "RefactorWorkOrder",
    "STANDARD_LEAN_AXIOMS",
    "count_effective_loc",
    "count_files_effective_loc",
    "find_lake_binary",
    "format_refactor_plan_markdown",
    "parse_check_signatures",
    "parse_print_axioms",
    "plan_refactors",
    "verify_refactor_gate",
]
