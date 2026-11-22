"""Import-safe, instance-aware Lean 4 proof pruning, multi-pass compression, and streaming archive materialization."""

from __future__ import annotations

import glob
import io
import json
import re
import sqlite3
import tarfile
import time
import zlib
from collections import Counter, defaultdict, deque
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterator, Sequence

from proof_compressor.analyze.consolidate import (
    ConsolidationOp,
    ConsolidationPlan,
    _compute_kept_import_dag,
    apply_consolidations_to_lines,
    plan_consolidation,
    verify_consolidation_plan_with_sources,
)
from proof_compressor.analyze.merge_modules import MergeReport, merge_project_modules
from proof_compressor.analyze.prune import resolve_roots
from proof_compressor.schema import connect_db, set_meta

VALID_MATERIALIZE_MODES = ("instance-aware", "import-closure", "decl-exact")

_CONFIG_FILENAMES = frozenset(
    {
        "lean-toolchain",
        "lakefile.toml",
        "lakefile.lean",
        "lake-manifest.json",
    }
)

_IMPLICIT_ATTR_RE = re.compile(
    r"@\[[^\]]*\b(?:simp|ext|aesop|norm_cast|push_cast|coe|positivity|measurability|"
    r"continuity|fun_prop|instance|default_instance|elab|macro|app_unexpander|delab|"
    r"to_additive|to_dual|simps|gcongr)\b"
    r"|(?:\blocal\s+instance\b|\bscoped\s+(?:notation|macro|elab|instance|attribute)\b"
    r"|\battribute\s*\[[^\]]*\b(?:simp|instance|ext|coe|to_additive)\b)",
    re.IGNORECASE,
)

_IN_PREFIX_END_RE = re.compile(r"\bin\s*(?:--.*)?$")
_IN_PREFIX_START_RE = re.compile(
    r"^(?:omit|include|open|set_option|attribute|variables?|universes?|local|scoped|classical|unseal)\b"
)
_STANDALONE_MOD_LINE_RE = re.compile(
    r"^(?:(?:private|protected|public|noncomputable|partial|unsafe|meta|scoped|local)\s*)+$"
)
_ATTR_OR_SCOPE_BARRIER_RE = re.compile(
    r"^(?:namespace|section|noncomputable\s+section|end|import|theorem|lemma|def|abbrev|"
    r"structure|class|inductive|instance|axiom|opaque|constant|example)\b"
)

_STRUCTURAL_LINE_RE = re.compile(
    r"^\s*(?:namespace\s+\S+|section(?:\s+\S+)?|end(?:\s+\S+)?)\s*(?:--.*)?$"
)

_IMPORT_LINE_RE = re.compile(
    r"^(\s*(?:(?:public|private|meta)\s+)*import\s+)([A-Za-z0-9_'.\u0080-\uffff]+)(\s*(?:--.*)?)$"
)
_ROOT_DOT_REF_RE = re.compile(
    r"_root_\.([A-Za-z_\u00c0-\u024f\u0370-\u03ff][A-Za-z0-9_'.\u0080-\uffff]*)"
)
_NAMESPACE_OPEN_LINE_RE = re.compile(r"^(\s*)(open(?:\s+scoped)?)(\s+)(.+)$")
_NAMESPACE_DECL_RE = re.compile(
    r"^\s*namespace\s+([A-Za-z0-9_'.\u0080-\uffff]+)\s*(?:--.*)?$"
)
_SECTION_OPEN_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_'.\u0080-\uffff]+))?\s*(?:--.*)?$"
)
_SCOPE_END_RE = re.compile(
    r"^\s*end(?:\s+([A-Za-z0-9_'.\u0080-\uffff]+))?\s*(?:--.*)?$"
)

# Lean / Std / Mathlib top-level namespaces that must never be stripped from `open ...`
# even if a project file also added a declaration inside one of them that was pruned.
_PROTECTED_MATHLIB_TOP_NS = frozenset(
    {
        "AddGroup",
        "AddMonoid",
        "AddMonoidHom",
        "AdicCompletion",
        "Affine",
        "Algebra",
        "AlgebraicGeometry",
        "AlgHom",
        "Array",
        "Artinian",
        "Associated",
        "Attribute",
        "BigOperators",
        "Bool",
        "Bornology",
        "Cardinal",
        "CategoryTheory",
        "Char",
        "CharZero",
        "Classical",
        "ClassGroup",
        "CliffordAlgebra",
        "Command",
        "CommRing",
        "Complex",
        "ComplexConjugate",
        "Congr",
        "ContinuousLinearMap",
        "Convolution",
        "Cyclotomic",
        "DedekindDomain",
        "Derivation",
        "Elab",
        "ENNReal",
        "Equiv",
        "EReal",
        "EuclideanDomain",
        "EuclideanGeometry",
        "ExteriorAlgebra",
        "Field",
        "Filter",
        "Fin",
        "Finset",
        "Fourier",
        "FractionalIdeal",
        "FreeAlgebra",
        "Function",
        "GaloisTheory",
        "Group",
        "HahnSeries",
        "Ideal",
        "Init",
        "InnerProductGeometry",
        "InnerProductSpace",
        "Int",
        "IO",
        "IsLocalization",
        "KaehlerDifferential",
        "Lattice",
        "LaurentSeries",
        "Lean",
        "LieAlgebra",
        "LieRing",
        "LinearAlgebra",
        "LinearMap",
        "List",
        "Localization",
        "Mathlib",
        "Matrix",
        "MeasureTheory",
        "Meta",
        "Metric",
        "MetricSpace",
        "Module",
        "Monoid",
        "MonoidHom",
        "Multiset",
        "MvPolynomial",
        "MvPowerSeries",
        "Nat",
        "NNReal",
        "Noetherian",
        "NormedSpace",
        "NumberField",
        "NumberTheory",
        "Option",
        "Order",
        "Ordinal",
        "Padic",
        "Parser",
        "Pointwise",
        "Polynomial",
        "PolynomialModule",
        "PowerSeries",
        "Presheaf",
        "PrimeSpectrum",
        "PrincipalIdealDomain",
        "ProbabilityTheory",
        "Prod",
        "ProjectiveGeometry",
        "Quotient",
        "Rat",
        "Real",
        "Rel",
        "Ring",
        "RingHom",
        "Scheme",
        "Scoped",
        "Set",
        "Sheaf",
        "SimpleGraph",
        "Std",
        "String",
        "Subgroup",
        "Submodule",
        "Submonoid",
        "Subring",
        "Sum",
        "Syntax",
        "Tactic",
        "TensorProduct",
        "TopologicalSpace",
        "Topology",
        "Ultrafilter",
        "UniformSpace",
        "UniqueFactorizationMonoid",
        "Units",
        "WithBot",
        "WithOne",
        "WithTop",
        "WithZero",
        "WittVector",
        "ZMod",
    }
)

_SAFE_STRIP_KINDS = frozenset({"theorem", "lemma"})
_IMPLICIT_KEEP_KINDS = frozenset({"instance", "class"})


@dataclass
class PrunePlan:
    """Computed module and declaration retention plan for a given pruning mode."""

    mode: str
    root_ids: list[int]
    root_names: list[str]
    root_module_ids: set[int]

    raw_project_modules: int
    import_closure_modules: set[int]
    decl_reachable_modules: set[int]
    instance_support_modules: set[int]
    barrel_bridge_modules: set[int]
    kept_modules: set[int]
    dropped_modules: set[int]

    kept_decl_ids: set[int]
    strippable_decl_ids_by_mod: dict[int, list[int]]

    mod_path: dict[int, str]
    mod_loc: dict[int, int]
    path_to_mid: dict[str, int]
    mod_imports: dict[int, list[int]]

    syntax_support_modules: set[int] = field(default_factory=set)
    collapsible_barrel_modules: set[int] = field(default_factory=set)
    collapsed_barrel_modules: set[int] = field(default_factory=set)
    zero_decl_modules: set[int] = field(default_factory=set)
    mod_external_imports: dict[int, list[str]] = field(default_factory=dict)
    needed_mod_bridges: dict[int, set[int]] = field(default_factory=dict)
    collapse_barrels: bool = False
    trans_ext_imports: dict[int, tuple[str, ...]] = field(default_factory=dict)
    dropped_only_namespaces: frozenset[str] = field(default_factory=frozenset)
    per_module_dropped_open_ns: dict[int, frozenset[str]] = field(default_factory=dict)


@dataclass
class TransformResult:
    """Detailed per-file transformation output and accounting."""

    text: str
    stripped_decls: int = 0
    stripped_nonblank_lines: int = 0
    dropped_imports: int = 0
    rewritten_imports: int = 0
    consolidated_decls: int = 0
    consolidated_saved_loc: int = 0
    stripped_comment_and_blank_lines: int = 0
    orig_total_lines: int = 0
    orig_nonblank_lines: int = 0
    final_total_lines: int = 0
    final_nonblank_lines: int = 0


@dataclass
class MaterializeReport:
    """Quantitative summary of import-safe / instance-aware pruning and multi-pass compression."""

    mode: str = "instance-aware"
    root_names: list[str] = field(default_factory=list)

    raw_modules: int = 0
    import_closure_modules: int = 0
    decl_reachable_modules: int = 0
    instance_support_modules: int = 0
    syntax_support_modules: int = 0
    barrel_bridge_modules: int = 0
    collapsed_barrel_modules: int = 0
    collapsed_barrel_loc: int = 0
    kept_modules: int = 0
    dropped_modules: int = 0
    module_reduction_pct: float = 0.0

    raw_loc: int = 0
    import_closure_loc: int = 0
    decl_reachable_loc: int = 0
    kept_modules_raw_loc: int = 0
    intra_module_stripped_loc: int = 0
    consolidated_duplicates: int = 0
    consolidated_saved_loc: int = 0
    hoistable_duplicate_groups: int = 0
    hoistable_redundant_decls: int = 0
    hoistable_estimated_saved_loc: int = 0
    stripped_comment_and_blank_lines: int = 0
    materialized_loc: int = 0
    final_nonblank_loc: int = 0
    final_total_lines: int = 0
    total_loc_reduction_pct: float = 0.0

    raw_declarations: int = 0
    reachable_declarations: int = 0
    instance_support_declarations: int = 0
    stripped_intra_module_declarations: int = 0
    kept_declarations: int = 0

    dropped_import_lines: int = 0
    rewritten_import_lines: int = 0
    files_written: int = 0
    config_files_copied: int = 0
    output_dir: str | None = None
    output_archive: str | None = None

    merge_modules_enabled: bool = False
    target_module_loc: int = 0
    pre_merge_modules: int = 0
    merged_output_modules: int = 0
    eliminated_import_lines_by_merge: int = 0
    loc_saved_by_merge: int = 0
    phase_b_consolidations: int = 0
    phase_b_saved_loc: int = 0
    merge_dangling_imports: int = 0
    merge_cycle_count: int = 0

    raw_archive_bytes: int = 0
    raw_uncompressed_bytes: int = 0
    compressed_uncompressed_bytes: int = 0
    output_archive_bytes: int = 0

    # Deep audit breakdown of imported-but-not-decl-reached modules
    unimported_dead_modules: int = 0
    unimported_dead_loc: int = 0
    imported_not_decl_reached_modules: int = 0
    imported_not_decl_reached_loc: int = 0
    imported_zero_decl_barrel_modules: int = 0
    imported_zero_decl_barrel_loc: int = 0
    imported_instance_class_modules: int = 0
    imported_instance_class_loc: int = 0
    imported_def_structure_modules: int = 0
    imported_def_structure_loc: int = 0
    imported_bookkeeping_lemma_modules: int = 0
    imported_bookkeeping_lemma_loc: int = 0
    imported_unused_theorem_modules: int = 0
    imported_unused_theorem_loc: int = 0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _open_db(db: sqlite3.Connection | str | Path) -> tuple[sqlite3.Connection, bool]:
    if isinstance(db, sqlite3.Connection):
        return db, False
    return connect_db(db), True


def _pct(part: int, whole: int) -> float:
    if whole <= 0:
        return 0.0
    return round(100.0 * part / whole, 2)


def _normalize_mod_name(raw_path: str) -> str:
    s = (raw_path or "").strip().replace("\\", "/")
    while s.startswith("./"):
        s = s[2:]
    for pref in ("lean/src/", "src/"):
        if s.startswith(pref):
            s = s[len(pref) :]
            break
    if s.endswith(".lean"):
        s = s[:-5]
    return s.replace("/", ".")


def is_pure_import_barrel_source(source_text: str) -> bool:
    """Return True iff every non-blank, non-comment line in ``source_text`` is an ``import`` line."""
    stripped_text, _ = strip_lean_comments(source_text, keep_docstrings=False)
    saw_import = False
    for line in stripped_text.splitlines():
        s = line.strip()
        if not s:
            continue
        if _IMPORT_LINE_RE.match(line):
            saw_import = True
            continue
        return False
    return saw_import


# ---------------------------------------------------------------------------
# Lean 4 syntax-safe comment & blank-line stripper
# ---------------------------------------------------------------------------


def _is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in ("_", "'") or ord(ch) >= 0x80


def strip_lean_comments(
    source_text: str,
    *,
    keep_docstrings: bool = False,
) -> tuple[str, int]:
    """Strip Lean 4 line comments (``--``) and nested block comments (``/- ... -/``)
    plus redundant blank lines without corrupting strings, char literals, guillemet
    identifiers, ``add_decl_doc`` docstrings, or layout indentation.

    Returns ``(new_source, removed_line_count)``.
    """
    if not source_text:
        return source_text, 0

    orig_lines = source_text.splitlines()
    n = len(source_text)
    out: list[str] = []
    i = 0

    while i < n:
        ch = source_text[i]

        # 1. Double-quoted string literal (handles `s!"..."` and `\"` / `\\` escapes)
        if ch == '"':
            start = i
            i += 1
            while i < n:
                c = source_text[i]
                if c == "\\" and i + 1 < n:
                    i += 2
                    continue
                if c == '"':
                    i += 1
                    break
                i += 1
            out.append(source_text[start:i])
            continue

        # 2. Guillemet-quoted identifier `«...»`
        if ch == "«":
            start = i
            end_g = source_text.find("»", i + 1)
            if end_g == -1:
                out.append(source_text[start:])
                i = n
            else:
                out.append(source_text[start : end_g + 1])
                i = end_g + 1
            continue

        # 3. Char literal `'c'` or `'\n'` or `'"'` (only when not prime suffix on an ident)
        if ch == "'" and (i == 0 or not _is_ident_char(source_text[i - 1])):
            if i + 3 < n and source_text[i + 1] == "\\" and source_text[i + 3] == "'":
                out.append(source_text[i : i + 4])
                i += 4
                continue
            if i + 2 < n and source_text[i + 1] not in ("\\", "'", "\n") and source_text[i + 2] == "'":
                out.append(source_text[i : i + 3])
                i += 3
                continue

        # 4. Line comment `-- ...`
        if ch == "-" and i + 1 < n and source_text[i + 1] == "-":
            nl = source_text.find("\n", i + 2)
            if nl == -1:
                i = n
            else:
                i = nl
            continue

        # 5. Nested block comment `/- ... -/` (and docstrings `/-- ... -/`, `/-! ... -/`)
        if ch == "/" and i + 1 < n and source_text[i + 1] == "-":
            block_start = i
            is_doc = i + 2 < n and source_text[i + 2] == "-"
            depth = 1
            i += 2
            while i < n and depth > 0:
                if source_text[i] == "/" and i + 1 < n and source_text[i + 1] == "-":
                    depth += 1
                    i += 2
                elif source_text[i] == "-" and i + 1 < n and source_text[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            block_end = i
            block_text = source_text[block_start:block_end]

            # Preserve docstrings when requested OR when immediately followed by `add_decl_doc`
            must_preserve = False
            if is_doc:
                if keep_docstrings:
                    must_preserve = True
                else:
                    probe = block_end
                    while probe < n and source_text[probe] in (" ", "\t", "\r", "\n"):
                        probe += 1
                    if source_text.startswith("add_decl_doc", probe):
                        must_preserve = True

            if must_preserve:
                out.append(block_text)
                continue

            # Replace stripped block comment without merging tokens or shifting code columns
            has_nl = "\n" in block_text
            if not has_nl:
                prev_ch = source_text[block_start - 1] if block_start > 0 else "\n"
                next_ch = source_text[block_end] if block_end < n else "\n"
                if prev_ch not in (" ", "\t", "\r", "\n") and next_ch not in (" ", "\t", "\r", "\n"):
                    out.append(" ")
            else:
                # Check if code precedes block_start on its line or follows block_end on its line
                ls = source_text.rfind("\n", 0, block_start)
                before_on_line = source_text[ls + 1 : block_start]
                le = source_text.find("\n", block_end)
                after_on_line = source_text[block_end : (n if le == -1 else le)]
                code_before = bool(before_on_line.strip())
                code_after = bool(after_on_line.strip())

                if code_before and code_after:
                    last_nl_in_blk = block_text.rfind("\n")
                    trailing_col = len(block_text) - last_nl_in_blk - 1
                    out.append("\n" + (" " * trailing_col))
                elif not code_before and code_after:
                    last_nl_in_blk = block_text.rfind("\n")
                    trailing_col = len(block_text) - last_nl_in_blk - 1
                    # Keep exact column offset for code after `-/` on the closing line
                    if before_on_line:
                        # Remove leading spaces already appended for the opening line
                        out.append("\n" + (" " * trailing_col))
                    else:
                        out.append(" " * trailing_col)
                # Otherwise (code_before and not code_after, or comment-only block):
                # emit nothing so the trailing newline closes the line cleanly.
            continue

        out.append(ch)
        i += 1

    stripped_raw = "".join(out)

    # Collapse redundant blank lines while preserving exact indentation of all code lines
    final_lines: list[str] = []
    prev_blank = True  # Drops leading blank lines
    for ln in stripped_raw.splitlines():
        clean_ln = ln.rstrip(" \t\r")
        if not clean_ln:
            if not prev_blank:
                final_lines.append("")
                prev_blank = True
        else:
            final_lines.append(clean_ln)
            prev_blank = False

    while final_lines and not final_lines[-1]:
        final_lines.pop()

    new_text = "\n".join(final_lines)
    if new_text and source_text.endswith("\n"):
        new_text += "\n"

    removed_lines = max(0, len(orig_lines) - len(final_lines))
    return new_text, removed_lines


# ---------------------------------------------------------------------------
# Pruning plan computation (with syntax-support & pure-barrel collapsing)
# ---------------------------------------------------------------------------


@dataclass
class _PruneGraphContext:
    """In-memory graph and declaration metadata retained for fixpoint closure and materialization."""

    project_mids: set[int]
    all_zero_decl_mods: set[int]
    mod_total_imp_count: Counter[int]
    mod_to_decls: dict[int, list[int]]
    decl_mod: dict[int, int]
    decl_kind: dict[int, str]
    decl_loc: dict[int, int]
    decl_name: dict[int, str]
    spans_by_mod: dict[int, list[tuple[int, int, int, bool]]]
    out_adj: dict[int, list[int]]
    mathlib_ns: set[str]
    all_proj_ns: set[str]
    extra_mod_edges: dict[int, set[int]] = field(default_factory=lambda: defaultdict(set))
    extra_kept_ns: set[str] = field(default_factory=set)
    restored_non_pure_barrels: set[int] = field(default_factory=set)


def _add_ns_prefixes(target: set[str], qualified_name: str) -> None:
    if not qualified_name or "." not in qualified_name:
        return
    parts = qualified_name.split(".")
    for i in range(1, len(parts)):
        target.add(".".join(parts[:i]))


def _compute_trans_ext_imports(
    project_mids: set[int],
    mod_imports: dict[int, list[int]],
    mod_external_imports: dict[int, list[str]],
) -> dict[int, tuple[str, ...]]:
    """Compute cycle-safe transitive external (e.g. Mathlib) imports per project module."""
    state: dict[int, int] = {}
    order: list[int] = []
    for start in project_mids:
        if state.get(start, 0) != 0:
            continue
        stack: list[tuple[int, int]] = [(start, 0)]
        state[start] = 1
        while stack:
            node, idx = stack[-1]
            nbs = mod_imports.get(node, ())
            if idx < len(nbs):
                stack[-1] = (node, idx + 1)
                nb = nbs[idx]
                if nb in project_mids and state.get(nb, 0) == 0:
                    state[nb] = 1
                    stack.append((nb, 0))
            else:
                stack.pop()
                state[node] = 2
                order.append(node)

    trans_ext: dict[int, tuple[str, ...]] = {}
    for m in order:
        exts: list[str] = []
        seen: set[str] = set()
        for e in mod_external_imports.get(m, ()):
            if e not in seen:
                seen.add(e)
                exts.append(e)
        for nb in mod_imports.get(m, ()):
            for e in trans_ext.get(nb, ()):
                if e not in seen:
                    seen.add(e)
                    exts.append(e)
        trans_ext[m] = tuple(exts)
    return trans_ext


def _is_anon_fallback_name(name: str) -> bool:
    """Return True for parser fallback ``anon_*`` names whose real identifier missed ASCII regexes."""
    short = name.rsplit(".", 1)[-1] if name else ""
    return short.startswith("anon_")


def _expand_instance_aware_closure(
    plan: PrunePlan,
    ctx: _PruneGraphContext,
    initial_seeds: Sequence[int],
) -> None:
    """Expand ``kept_decl_ids`` and ``kept_modules`` transitively across all kept non-theorem
    declarations, syntax-support modules, and (if not collapsed) zero-decl barrel bridges.
    """
    q_decls: deque[int] = deque()
    for did in initial_seeds:
        if did not in plan.kept_decl_ids:
            plan.kept_decl_ids.add(did)
        q_decls.append(did)
        dm = ctx.decl_mod.get(did)
        if dm is not None and dm in ctx.project_mids and dm not in plan.kept_modules:
            plan.collapsed_barrel_modules.discard(dm)
            plan.kept_modules.add(dm)
            for d2 in ctx.mod_to_decls.get(dm, ()):
                if d2 not in plan.kept_decl_ids and (
                    ctx.decl_kind[d2] not in _SAFE_STRIP_KINDS
                    or _is_anon_fallback_name(ctx.decl_name.get(d2, ""))
                ):
                    plan.kept_decl_ids.add(d2)
                    q_decls.append(d2)

    changed = True
    while changed:
        changed = False
        while q_decls:
            u = q_decls.popleft()
            for v in ctx.out_adj.get(u, ()):
                if v not in plan.kept_decl_ids:
                    plan.kept_decl_ids.add(v)
                    q_decls.append(v)
                    changed = True
                    vm = ctx.decl_mod.get(v)
                    if vm is not None and vm in ctx.project_mids and vm not in plan.kept_modules:
                        plan.collapsed_barrel_modules.discard(vm)
                        plan.kept_modules.add(vm)
                        for d2 in ctx.mod_to_decls.get(vm, ()):
                            if d2 not in plan.kept_decl_ids and (
                                ctx.decl_kind[d2] not in _SAFE_STRIP_KINDS
                                or _is_anon_fallback_name(ctx.decl_name.get(d2, ""))
                            ):
                                plan.kept_decl_ids.add(d2)
                                q_decls.append(d2)

        # Expand zero-decl syntax/tactic/notation modules imported directly or via zero-decl barrels
        q_syn: deque[int] = deque(plan.kept_modules)
        vis_syn: set[int] = set(plan.kept_modules)
        while q_syn:
            cur_m = q_syn.popleft()
            for nb in plan.mod_imports.get(cur_m, ()):
                if nb in vis_syn:
                    continue
                if nb in ctx.all_zero_decl_mods:
                    vis_syn.add(nb)
                    if (
                        plan.mod_loc[nb] > ctx.mod_total_imp_count[nb]
                        and nb not in plan.collapsed_barrel_modules
                    ):
                        if nb not in plan.kept_modules:
                            plan.syntax_support_modules.add(nb)
                            plan.kept_modules.add(nb)
                            changed = True
                    q_syn.append(nb)

    if not plan.collapse_barrels:
        added_barrel = True
        while added_barrel:
            added_barrel = False
            for m in ctx.all_zero_decl_mods:
                if m in plan.kept_modules:
                    continue
                if any(nb in plan.kept_modules for nb in plan.mod_imports.get(m, ())):
                    plan.barrel_bridge_modules.add(m)
                    plan.kept_modules.add(m)
                    added_barrel = True
    else:
        pure_candidates = {
            m
            for m in ctx.all_zero_decl_mods
            if m not in plan.root_module_ids
            and m not in ctx.restored_non_pure_barrels
            and m not in plan.kept_modules
            and plan.mod_loc[m] > 0
            and plan.mod_loc[m] == ctx.mod_total_imp_count[m]
        }
        q_b: deque[int] = deque(plan.kept_modules)
        vis_b: set[int] = set(plan.kept_modules)
        while q_b:
            cur_m = q_b.popleft()
            for nb in plan.mod_imports.get(cur_m, ()):
                if nb in vis_b:
                    continue
                if nb in pure_candidates:
                    vis_b.add(nb)
                    plan.collapsible_barrel_modules.add(nb)
                    plan.collapsed_barrel_modules.add(nb)
                    q_b.append(nb)

    plan.dropped_modules = ctx.project_mids - plan.kept_modules
    strippable_by_mod: dict[int, list[int]] = defaultdict(list)
    for m in plan.kept_modules:
        for d in ctx.mod_to_decls.get(m, ()):
            if (
                d not in plan.kept_decl_ids
                and ctx.decl_kind[d] in _SAFE_STRIP_KINDS
                and not _is_anon_fallback_name(ctx.decl_name.get(d, ""))
            ):
                strippable_by_mod[m].append(d)
    plan.strippable_decl_ids_by_mod = dict(strippable_by_mod)


def _finalize_bridges_and_namespaces(
    plan: PrunePlan,
    ctx: _PruneGraphContext,
) -> None:
    """Recompute ``needed_mod_bridges``, ``trans_ext_imports``, and ``dropped_only_namespaces``."""
    dropped_zero_barrels = (
        ctx.all_zero_decl_mods - plan.kept_modules
    ) | plan.collapsed_barrel_modules
    _, mid_to_bit, trans_kept = _compute_kept_import_dag(
        plan.kept_modules,
        plan.mod_imports,
        collapsed_barrels=dropped_zero_barrels,
    )
    needed_mod_bridges: dict[int, set[int]] = defaultdict(set)
    for src_id in plan.kept_decl_ids:
        sm = ctx.decl_mod.get(src_id)
        if sm is None or sm not in plan.kept_modules:
            continue
        sm_bits = trans_kept.get(sm, 0)
        for dst_id in ctx.out_adj.get(src_id, ()):
            if dst_id not in plan.kept_decl_ids:
                continue
            dm = ctx.decl_mod.get(dst_id)
            if dm is None or dm == sm or dm not in plan.kept_modules:
                continue
            if not (sm_bits & mid_to_bit[dm]):
                needed_mod_bridges[sm].add(dm)

    for sm, targets in ctx.extra_mod_edges.items():
        if sm not in plan.kept_modules:
            continue
        sm_bits = trans_kept.get(sm, 0)
        for dm in targets:
            if dm == sm or dm not in plan.kept_modules:
                continue
            if not (sm_bits & mid_to_bit[dm]):
                needed_mod_bridges[sm].add(dm)

    plan.needed_mod_bridges = dict(needed_mod_bridges)
    plan.trans_ext_imports = _compute_trans_ext_imports(
        ctx.project_mids,
        plan.mod_imports,
        plan.mod_external_imports,
    )

    kept_ns: set[str] = set(ctx.extra_kept_ns)
    for did in plan.kept_decl_ids:
        _add_ns_prefixes(kept_ns, ctx.decl_name.get(did, ""))
    kept_segments: set[str] = set()
    for ns in kept_ns:
        for seg in ns.split("."):
            kept_segments.add(seg)

    dropped_only_ns: set[str] = set()
    for ns in ctx.all_proj_ns:
        if ns in kept_ns or ns in ctx.mathlib_ns:
            continue
        first_seg = ns.split(".", 1)[0]
        if first_seg in _PROTECTED_MATHLIB_TOP_NS:
            continue
        if "." not in ns and ns in kept_segments:
            continue
        dropped_only_ns.add(ns)
    plan.dropped_only_namespaces = frozenset(dropped_only_ns)


def _sync_report_from_plan(
    report: MaterializeReport,
    plan: PrunePlan,
    ctx: _PruneGraphContext,
) -> None:
    """Synchronize ``MaterializeReport`` counters with a converged ``PrunePlan``."""
    stripped_intra_loc = 0
    stripped_intra_cnt = 0
    for m, dlist in plan.strippable_decl_ids_by_mod.items():
        if m not in plan.kept_modules:
            continue
        for d in dlist:
            stripped_intra_cnt += 1
            stripped_intra_loc += ctx.decl_loc.get(d, 0)

    kept_raw_loc = sum(plan.mod_loc[m] for m in plan.kept_modules)
    collapsed_barrel_loc = sum(plan.mod_loc[m] for m in plan.collapsed_barrel_modules)
    est_mat_loc = max(0, kept_raw_loc - stripped_intra_loc)

    report.syntax_support_modules = len(
        plan.syntax_support_modules - plan.decl_reachable_modules - plan.instance_support_modules
    )
    report.barrel_bridge_modules = len(
        (plan.barrel_bridge_modules - plan.collapsed_barrel_modules)
        - plan.decl_reachable_modules
        - plan.instance_support_modules
        - plan.syntax_support_modules
    )
    report.collapsed_barrel_modules = len(plan.collapsed_barrel_modules)
    report.collapsed_barrel_loc = collapsed_barrel_loc
    report.kept_modules = len(plan.kept_modules)
    report.dropped_modules = len(plan.dropped_modules)
    report.module_reduction_pct = _pct(len(plan.dropped_modules), report.raw_modules)
    report.kept_modules_raw_loc = kept_raw_loc
    report.intra_module_stripped_loc = stripped_intra_loc
    report.materialized_loc = est_mat_loc
    report.final_nonblank_loc = est_mat_loc
    report.total_loc_reduction_pct = _pct(report.raw_loc - est_mat_loc, report.raw_loc)
    report.stripped_intra_module_declarations = stripped_intra_cnt
    report.kept_declarations = len(plan.kept_decl_ids)


def _compute_prune_plan_with_ctx(
    conn: sqlite3.Connection,
    *,
    roots: Sequence[str] | None = None,
    mode: str = "instance-aware",
    collapse_barrels: bool = False,
) -> tuple[PrunePlan, MaterializeReport, _PruneGraphContext]:
    if mode not in VALID_MATERIALIZE_MODES:
        raise ValueError(f"Unsupported mode {mode!r}; choose from {VALID_MATERIALIZE_MODES}")

    cur = conn.cursor()

    mod_path: dict[int, str] = {}
    mod_loc: dict[int, int] = {}
    mod_is_ml: dict[int, int] = {}
    path_to_mid: dict[str, int] = {}

    for mid, path, loc, is_ml in cur.execute(
        "SELECT id, path, loc, is_mathlib FROM modules"
    ):
        mid_i = int(mid)
        p = path or ""
        mod_path[mid_i] = p
        mod_loc[mid_i] = int(loc or 0)
        mod_is_ml[mid_i] = int(is_ml or 0)
        if p:
            path_to_mid[p] = mid_i
            path_to_mid[_normalize_mod_name(p)] = mid_i

    project_mids = {m for m, ml in mod_is_ml.items() if ml == 0}

    # Load module_imports (both project-to-project and external/Mathlib imports)
    mod_imports: dict[int, list[int]] = defaultdict(list)
    mod_external_imports: dict[int, list[str]] = defaultdict(list)
    mod_total_imp_count: Counter[int] = Counter()

    for src_mid, dst_path, dst_mid in cur.execute(
        "SELECT src_module_id, dst_module_path, dst_module_id FROM module_imports"
    ):
        sm = int(src_mid)
        if sm not in project_mids:
            continue
        mod_total_imp_count[sm] += 1
        tmid = int(dst_mid) if dst_mid is not None else path_to_mid.get(dst_path or "")
        if tmid is None and dst_path:
            tmid = path_to_mid.get(_normalize_mod_name(dst_path))
        if tmid is not None and tmid in project_mids:
            mod_imports[sm].append(tmid)
        elif dst_path:
            mod_external_imports[sm].append(dst_path)

    # Load declarations (single pass for project + Mathlib namespaces + line spans)
    decl_mod: dict[int, int] = {}
    decl_kind: dict[int, str] = {}
    decl_loc: dict[int, int] = {}
    decl_bk: dict[int, int] = {}
    decl_name: dict[int, str] = {}
    mod_to_decls: dict[int, list[int]] = defaultdict(list)
    mod_kinds: dict[int, Counter[str]] = defaultdict(Counter)
    mod_bk_cnt: Counter[int] = Counter()
    spans_by_mod: dict[int, list[tuple[int, int, int, bool]]] = defaultdict(list)
    mathlib_ns: set[str] = set()
    all_proj_ns: set[str] = set()

    for did, name, mid, kind, bloc, is_ml, is_bk, s_line, e_line in cur.execute(
        "SELECT id, name, module_id, kind, body_loc, is_mathlib, is_bookkeeping, "
        "start_line, end_line FROM declarations"
    ):
        nm = name or ""
        if int(is_ml or 0) != 0:
            _add_ns_prefixes(mathlib_ns, nm)
            continue
        did_i = int(did)
        mid_i = int(mid or 0)
        k = (kind or "").lower()
        bl = int(bloc or 0)
        bk = int(is_bk or 0)
        decl_mod[did_i] = mid_i
        decl_kind[did_i] = k
        decl_loc[did_i] = bl
        decl_bk[did_i] = bk
        decl_name[did_i] = nm
        mod_to_decls[mid_i].append(did_i)
        mod_kinds[mid_i][k] += 1
        if bk:
            mod_bk_cnt[mid_i] += 1
        spans_by_mod[mid_i].append(
            (did_i, int(s_line or 0), int(e_line or 0), k in _SAFE_STRIP_KINDS)
        )
        _add_ns_prefixes(all_proj_ns, nm)

    resolved_roots = resolve_roots(conn, roots)
    root_ids = [r[0] for r in resolved_roots]
    root_names = [r[1] for r in resolved_roots]
    root_mod_ids = {
        decl_mod[rid] for rid in root_ids if rid in decl_mod and decl_mod[rid] in project_mids
    }

    # Build declaration outgoing adjacency (src -> dst) restricted to project decls
    out_adj: dict[int, list[int]] = defaultdict(list)
    prev_s = -1
    prev_d = -1
    for src_id, dst_id in cur.execute(
        "SELECT src_id, dst_id FROM edges ORDER BY src_id, dst_id"
    ):
        if src_id == dst_id or (src_id == prev_s and dst_id == prev_d):
            continue
        prev_s = src_id
        prev_d = dst_id
        if src_id in decl_mod and dst_id in decl_mod:
            out_adj[src_id].append(dst_id)

    # 1. Exact declaration reachability BFS from root_ids
    decl_reach: set[int] = set()
    q_decl: deque[int] = deque()
    for rid in root_ids:
        if rid in decl_mod and rid not in decl_reach:
            decl_reach.add(rid)
            q_decl.append(rid)
    while q_decl:
        u = q_decl.popleft()
        for v in out_adj.get(u, ()):
            if v not in decl_reach:
                decl_reach.add(v)
                q_decl.append(v)

    decl_reach_mods = {
        decl_mod[d] for d in decl_reach if decl_mod[d] in project_mids
    } | root_mod_ids

    # 2. Transitive module-import closure from root_mod_ids
    imp_closure: set[int] = set()
    q_mod: deque[int] = deque()
    seed_mods = root_mod_ids if root_mod_ids else decl_reach_mods
    for m in seed_mods:
        if m in project_mids and m not in imp_closure:
            imp_closure.add(m)
            q_mod.append(m)
    while q_mod:
        m = q_mod.popleft()
        for nb in mod_imports.get(m, ()):
            if nb not in imp_closure:
                imp_closure.add(nb)
                q_mod.append(nb)

    imp_closure_or_decl = imp_closure | decl_reach_mods

    # 3. Classify imported-but-not-decl-reached modules
    diff_mods = imp_closure - decl_reach_mods
    unimported_mods = project_mids - imp_closure_or_decl

    zero_decl_mods: set[int] = set()
    instance_class_mods: set[int] = set()
    def_struct_mods: set[int] = set()
    bk_lemma_mods: set[int] = set()
    unused_thm_mods: set[int] = set()

    for m in diff_mods:
        dlist = mod_to_decls.get(m, [])
        if not dlist:
            zero_decl_mods.add(m)
        elif mod_kinds[m]["instance"] > 0 or mod_kinds[m]["class"] > 0:
            instance_class_mods.add(m)
        elif any(
            mod_kinds[m][k] > 0
            for k in ("def", "abbrev", "structure", "inductive", "axiom", "opaque", "constant")
        ):
            def_struct_mods.add(m)
        elif mod_bk_cnt[m] > 0:
            bk_lemma_mods.add(m)
        else:
            unused_thm_mods.add(m)

    all_zero_decl_mods = {m for m in project_mids if not mod_to_decls.get(m)}

    # 4. In instance-aware mode:
    # Keep decl_reach_mods + transitively imported instance/class support modules
    # + directly/transitively imported zero-decl syntax/tactic/export modules (e.g. BuildAid.D1..D4)
    # + zero-decl barrel bridges (unless --collapse-barrels collapses pure import-only barrels).
    instance_support_decls: set[int] = set()
    instance_support_mods: set[int] = set()
    syntax_support_mods: set[int] = set()
    barrel_bridge_mods: set[int] = set()

    if mode in ("instance-aware", "import-closure"):
        q_inst: deque[int] = deque()
        for m in imp_closure_or_decl:
            if mod_kinds[m]["instance"] > 0 or mod_kinds[m]["class"] > 0:
                instance_support_mods.add(m)
                for d in mod_to_decls.get(m, ()):
                    if (
                        decl_kind[d] in _IMPLICIT_KEEP_KINDS
                        and d not in decl_reach
                        and d not in instance_support_decls
                    ):
                        instance_support_decls.add(d)
                        q_inst.append(d)

        while q_inst:
            u = q_inst.popleft()
            for v in out_adj.get(u, ()):
                if v not in decl_reach and v not in instance_support_decls:
                    instance_support_decls.add(v)
                    instance_support_mods.add(decl_mod[v])
                    q_inst.append(v)

        core_kept = set(decl_reach_mods | instance_support_mods)

        q_syn: deque[int] = deque(core_kept)
        visited_syn: set[int] = set(core_kept)
        while q_syn:
            cur_m = q_syn.popleft()
            for nb in mod_imports.get(cur_m, ()):
                if nb in visited_syn:
                    continue
                if nb in zero_decl_mods:
                    visited_syn.add(nb)
                    if mod_loc[nb] > mod_total_imp_count[nb]:
                        syntax_support_mods.add(nb)
                        core_kept.add(nb)
                    q_syn.append(nb)

        added_barrel = True
        while added_barrel:
            added_barrel = False
            for m in zero_decl_mods:
                if m in core_kept:
                    continue
                if m not in barrel_bridge_mods and any(
                    nb in core_kept or nb in barrel_bridge_mods
                    for nb in mod_imports.get(m, ())
                ):
                    barrel_bridge_mods.add(m)
                    added_barrel = True

    if mode == "import-closure":
        kept_modules = set(imp_closure_or_decl)
    elif mode == "instance-aware":
        kept_modules = decl_reach_mods | instance_support_mods | syntax_support_mods | barrel_bridge_mods
    else:  # decl-exact
        kept_modules = set(decl_reach_mods)

    collapsible_barrels: set[int] = {
        m
        for m in kept_modules
        if m not in root_mod_ids
        and not mod_to_decls.get(m)
        and mod_loc[m] > 0
        and mod_loc[m] == mod_total_imp_count[m]
    }

    collapsed_barrels: set[int] = set()
    if collapse_barrels and collapsible_barrels:
        collapsed_barrels = set(collapsible_barrels)
        kept_modules = kept_modules - collapsed_barrels

    dropped_modules = project_mids - kept_modules
    kept_decl_ids = set(decl_reach) | set(instance_support_decls)
    non_strippable_seeds: list[int] = []
    strippable_by_mod: dict[int, list[int]] = defaultdict(list)

    for m in kept_modules:
        for d in mod_to_decls.get(m, ()):
            if d in kept_decl_ids:
                continue
            if decl_kind[d] in _SAFE_STRIP_KINDS and not _is_anon_fallback_name(
                decl_name.get(d, "")
            ):
                strippable_by_mod[m].append(d)
            else:
                kept_decl_ids.add(d)
                non_strippable_seeds.append(d)

    ctx = _PruneGraphContext(
        project_mids=project_mids,
        all_zero_decl_mods=all_zero_decl_mods,
        mod_total_imp_count=mod_total_imp_count,
        mod_to_decls=dict(mod_to_decls),
        decl_mod=decl_mod,
        decl_kind=decl_kind,
        decl_loc=decl_loc,
        decl_name=decl_name,
        spans_by_mod=dict(spans_by_mod),
        out_adj=dict(out_adj),
        mathlib_ns=mathlib_ns,
        all_proj_ns=all_proj_ns,
    )

    plan = PrunePlan(
        mode=mode,
        root_ids=root_ids,
        root_names=root_names,
        root_module_ids=root_mod_ids,
        raw_project_modules=len(project_mids),
        import_closure_modules=imp_closure_or_decl,
        decl_reachable_modules=decl_reach_mods,
        instance_support_modules=instance_support_mods,
        barrel_bridge_modules=barrel_bridge_mods,
        kept_modules=kept_modules,
        dropped_modules=dropped_modules,
        kept_decl_ids=kept_decl_ids,
        strippable_decl_ids_by_mod=dict(strippable_by_mod),
        mod_path=mod_path,
        mod_loc=mod_loc,
        path_to_mid=path_to_mid,
        mod_imports=dict(mod_imports),
        syntax_support_modules=syntax_support_mods,
        collapsible_barrel_modules=collapsible_barrels,
        collapsed_barrel_modules=collapsed_barrels,
        zero_decl_modules=all_zero_decl_mods,
        mod_external_imports=dict(mod_external_imports),
        collapse_barrels=collapse_barrels,
    )

    # Gap 1 fix: In instance-aware mode, transitively close out_adj from all kept
    # non-theorem declarations (def, structure, abbrev, class, instance, inductive, etc.)
    if mode == "instance-aware" and non_strippable_seeds:
        _expand_instance_aware_closure(plan, ctx, non_strippable_seeds)

    raw_loc = sum(mod_loc[m] for m in project_mids)
    imp_loc = sum(mod_loc[m] for m in imp_closure_or_decl)
    decl_loc_sum = sum(mod_loc[m] for m in decl_reach_mods)

    report = MaterializeReport(
        mode=mode,
        root_names=root_names,
        raw_modules=len(project_mids),
        import_closure_modules=len(imp_closure_or_decl),
        decl_reachable_modules=len(decl_reach_mods),
        instance_support_modules=len(instance_support_mods - decl_reach_mods),
        raw_loc=raw_loc,
        import_closure_loc=imp_loc,
        decl_reachable_loc=decl_loc_sum,
        raw_declarations=len(decl_mod),
        reachable_declarations=len(decl_reach),
        instance_support_declarations=len(instance_support_decls),
        unimported_dead_modules=len(unimported_mods),
        unimported_dead_loc=sum(mod_loc[m] for m in unimported_mods),
        imported_not_decl_reached_modules=len(diff_mods),
        imported_not_decl_reached_loc=sum(mod_loc[m] for m in diff_mods),
        imported_zero_decl_barrel_modules=len(zero_decl_mods),
        imported_zero_decl_barrel_loc=sum(mod_loc[m] for m in zero_decl_mods),
        imported_instance_class_modules=len(instance_class_mods),
        imported_instance_class_loc=sum(mod_loc[m] for m in instance_class_mods),
        imported_def_structure_modules=len(def_struct_mods),
        imported_def_structure_loc=sum(mod_loc[m] for m in def_struct_mods),
        imported_bookkeeping_lemma_modules=len(bk_lemma_mods),
        imported_bookkeeping_lemma_loc=sum(mod_loc[m] for m in bk_lemma_mods),
        imported_unused_theorem_modules=len(unused_thm_mods),
        imported_unused_theorem_loc=sum(mod_loc[m] for m in unused_thm_mods),
    )
    _sync_report_from_plan(report, plan, ctx)
    _finalize_bridges_and_namespaces(plan, ctx)
    return plan, report, ctx


def compute_prune_plan(
    db: sqlite3.Connection | str | Path,
    *,
    roots: Sequence[str] | None = None,
    mode: str = "instance-aware",
    collapse_barrels: bool = False,
) -> tuple[PrunePlan, MaterializeReport]:
    """Compute exact module and declaration retention plan under the chosen pruning mode."""
    conn, should_close = _open_db(db)
    try:
        plan, report, _ = _compute_prune_plan_with_ctx(
            conn,
            roots=roots,
            mode=mode,
            collapse_barrels=collapse_barrels,
        )
        return plan, report
    finally:
        if should_close:
            conn.close()


def _replacement_imports_for_dropped(
    caller_mid: int,
    dropped_mid: int,
    plan: PrunePlan,
    *,
    covered_ext: set[str] | None = None,
) -> list[str]:
    """Compute minimal, sound replacement imports when ``caller_mid`` imported ``dropped_mid``.

    - If ``dropped_mid`` is a collapsed/dropped pure zero-declaration barrel: traverse ONLY
      through zero-declaration barrels to splice all live kept project imports and external
      (Mathlib) imports, NEVER descending into pruned dead mathematical branches (such as
      ``SmallClassNumbers.*``).
    - If ``dropped_mid`` is a pruned non-barrel module: splice ONLY kept modules ``K`` that
      ``caller_mid`` actually references via declaration edges (``plan.needed_mod_bridges``)
      and were transitively imported through ``dropped_mid``, PLUS any transitive external
      (Mathlib) imports from ``dropped_mid`` not already covered by ``caller_mid``'s kept imports.
    """
    found: list[str] = []
    seen_names: set[str] = set()
    local_covered: set[str] = set(covered_ext) if covered_ext else set()
    dropped_barrels = (plan.zero_decl_modules - plan.kept_modules) | plan.collapsed_barrel_modules

    if dropped_mid in dropped_barrels:
        visited: set[int] = {dropped_mid}
        q: deque[int] = deque([dropped_mid])
        pending_ext: list[str] = []
        while q:
            cur = q.popleft()
            for ext_imp in plan.mod_external_imports.get(cur, ()):
                pending_ext.append(ext_imp)
            for nb in plan.mod_imports.get(cur, ()):
                if nb in visited:
                    continue
                visited.add(nb)
                if nb in plan.kept_modules:
                    norm_nb = _normalize_mod_name(plan.mod_path[nb])
                    if norm_nb not in seen_names:
                        seen_names.add(norm_nb)
                        found.append(norm_nb)
                        local_covered.update(plan.trans_ext_imports.get(nb, ()))
                elif nb in dropped_barrels:
                    q.append(nb)
        for ext_imp in pending_ext:
            if ext_imp not in local_covered and ext_imp not in seen_names:
                seen_names.add(ext_imp)
                found.append(ext_imp)
        return found

    # Non-barrel dropped intermediate: splice kept targets genuinely needed by caller_mid
    # AND preserve transitive external (Mathlib) imports if not already covered.
    needed = plan.needed_mod_bridges.get(caller_mid)
    if needed:
        visited_nb: set[int] = {dropped_mid}
        q_nb: deque[int] = deque([dropped_mid])
        remaining = set(needed)
        while q_nb and remaining:
            cur = q_nb.popleft()
            for nb in plan.mod_imports.get(cur, ()):
                if nb in visited_nb:
                    continue
                visited_nb.add(nb)
                if nb in plan.kept_modules:
                    if nb in remaining:
                        remaining.remove(nb)
                        norm_nb = _normalize_mod_name(plan.mod_path[nb])
                        if norm_nb not in seen_names:
                            seen_names.add(norm_nb)
                            found.append(norm_nb)
                            local_covered.update(plan.trans_ext_imports.get(nb, ()))
                else:
                    q_nb.append(nb)

    for ext_imp in plan.trans_ext_imports.get(dropped_mid, ()):
        if ext_imp not in local_covered and ext_imp not in seen_names:
            seen_names.add(ext_imp)
            found.append(ext_imp)
    return found


def _expand_decl_prefix_upward(
    lines: Sequence[str],
    s0: int,
    kept_line_mask: bytearray,
) -> int:
    """Expand a dead declaration's start index upward to include attached multi-line
    ``@[...]`` attributes, ``... in`` prefix commands (``omit``, ``include``, ``open``,
    ``variable``, ``set_option``, ``attribute``), standalone modifiers, and ``/-- ... -/``
    docstrings so stripping the declaration never leaves orphaned syntax prefixes."""
    ext = s0
    while ext > 0:
        # Probe backward over blank lines only if an attached prefix lives above them
        probe = ext - 1
        while probe >= 0 and not lines[probe].strip():
            if kept_line_mask[probe]:
                return ext
            probe -= 1
        if probe < 0 or kept_line_mask[probe]:
            break

        st = lines[probe].strip()

        # 1. Single-line or multi-line `@[...]` attribute block
        if st.startswith("@["):
            ext = probe
            continue
        if st.endswith("]") and not st.startswith(("--", "/-", "-/")):
            p = probe - 1
            found_attr = False
            while p >= 0 and not kept_line_mask[p]:
                pst = lines[p].strip()
                if pst.startswith("@["):
                    found_attr = True
                    break
                if _ATTR_OR_SCOPE_BARRIER_RE.match(pst) or _IN_PREFIX_END_RE.search(pst):
                    break
                p -= 1
            if found_attr:
                ext = p
                continue

        # 2. Standalone modifier lines (`private`, `noncomputable`, etc.)
        if _STANDALONE_MOD_LINE_RE.match(st):
            ext = probe
            continue

        # 3. Single-line or multi-line `... in` prefix commands
        if _IN_PREFIX_END_RE.search(st) and not st.startswith("--"):
            p = probe
            while p > 0 and not kept_line_mask[p] and (
                not lines[p].strip() or lines[p][0] in (" ", "\t")
            ):
                p -= 1
            if not kept_line_mask[p] and _IN_PREFIX_START_RE.match(lines[p].strip()):
                ext = p
                continue

        # 4. Attached `/-- ... -/` docstring
        if st.endswith("-/"):
            doc_s = probe
            while doc_s >= 0 and not kept_line_mask[doc_s]:
                if "/--" in lines[doc_s]:
                    ext = doc_s
                    break
                if doc_s < probe and ("/-" in lines[doc_s] or "-/" in lines[doc_s]):
                    break
                doc_s -= 1
            if ext == doc_s:
                continue

        break
    return ext


def _compute_strip_line_mask(
    lines: Sequence[str],
    decl_spans: Sequence[tuple[int, int, int, bool]],
    kept_decl_ids: set[int],
) -> tuple[bytearray, int]:
    """Compute 0-based line mask for intra-module dead theorems/lemmas in ``decl_spans``."""
    n_lines = len(lines)
    strip_line_mask = bytearray(n_lines)
    stripped_decls = 0
    if not decl_spans or n_lines == 0:
        return strip_line_mask, stripped_decls

    kept_line_mask = bytearray(n_lines)
    for did, s_line, e_line, is_strip_cand in decl_spans:
        if not is_strip_cand or did in kept_decl_ids:
            s0 = max(0, s_line - 1)
            e0 = min(n_lines - 1, max(s0, e_line - 1))
            while e0 > s0:
                est = lines[e0].strip()
                if not est or _STANDALONE_MOD_LINE_RE.match(est) or est.startswith("@["):
                    e0 -= 1
                    continue
                if _IN_PREFIX_END_RE.search(est) and not est.startswith("--"):
                    p = e0
                    while p > s0 and (not lines[p].strip() or lines[p][0] in (" ", "\t")):
                        p -= 1
                    if p > s0 and _IN_PREFIX_START_RE.match(lines[p].strip()):
                        e0 = p - 1
                        continue
                break
            for idx in range(s0, e0 + 1):
                kept_line_mask[idx] = 1

    for did, s_line, e_line, is_strip_cand in decl_spans:
        if not is_strip_cand or did in kept_decl_ids:
            continue
        if s_line <= 0 or e_line < s_line:
            continue
        s0 = max(0, s_line - 1)
        e0 = min(n_lines - 1, e_line - 1)
        ext_s0 = _expand_decl_prefix_upward(lines, s0, kept_line_mask)
        if any(kept_line_mask[i] for i in range(ext_s0, e0 + 1)):
            continue
        block_text = "\n".join(lines[ext_s0 : e0 + 1])
        if _IMPLICIT_ATTR_RE.search(block_text):
            continue
        for i in range(ext_s0, e0 + 1):
            if not _STRUCTURAL_LINE_RE.match(lines[i]):
                strip_line_mask[i] = 1
        stripped_decls += 1

    return strip_line_mask, stripped_decls


def _collect_declared_namespaces(source_text: str) -> set[str]:
    """Collect all explicit ``namespace ...`` names (and nested prefixes) declared in source."""
    found: set[str] = set()
    ns_stack: list[tuple[str, str | None]] = []
    for line in source_text.splitlines():
        if m_ns := _NAMESPACE_DECL_RE.match(line):
            nm = m_ns.group(1)
            ns_stack.append(("ns", nm))
            cur_full = ".".join(v for k, v in ns_stack if k == "ns" and v)
            if cur_full:
                parts = cur_full.split(".")
                for i in range(1, len(parts) + 1):
                    found.add(".".join(parts[:i]))
        elif m_sec := _SECTION_OPEN_RE.match(line):
            ns_stack.append(("sec", m_sec.group(1)))
        elif m_end := _SCOPE_END_RE.match(line):
            enm = m_end.group(1)
            if not ns_stack:
                continue
            if enm is None:
                ns_stack.pop()
            else:
                for i in range(len(ns_stack) - 1, -1, -1):
                    if ns_stack[i][1] == enm:
                        del ns_stack[i:]
                        break
    return found


def _update_scope_stack(ns_stack: list[tuple[str, str | None]], line: str) -> None:
    if m_ns := _NAMESPACE_DECL_RE.match(line):
        ns_stack.append(("ns", m_ns.group(1)))
    elif m_sec := _SECTION_OPEN_RE.match(line):
        ns_stack.append(("sec", m_sec.group(1)))
    elif m_end := _SCOPE_END_RE.match(line):
        enm = m_end.group(1)
        if not ns_stack:
            return
        if enm is None:
            ns_stack.pop()
        else:
            for i in range(len(ns_stack) - 1, -1, -1):
                if ns_stack[i][1] == enm:
                    del ns_stack[i:]
                    return


def _rewrite_open_line(
    line: str,
    cur_ns_prefix: str,
    dropped_only_ns: frozenset[str],
    mod_dropped_open: frozenset[str] | None = None,
) -> tuple[str | None, bool]:
    """Strip dropped-only or per-module unimported project namespace tokens from ``open ...``."""
    m = _NAMESPACE_OPEN_LINE_RE.match(line)
    if not m:
        return line, False
    indent, open_kw, sp, rest = m.group(1), m.group(2), m.group(3), m.group(4)

    comment_suffix = ""
    if "--" in rest:
        idx = rest.find("--")
        comment_suffix = rest[idx:]
        rest_no_cmt = rest[:idx]
    else:
        rest_no_cmt = rest

    trailing_ws = ""
    stripped_no_cmt = rest_no_cmt.rstrip()
    if len(stripped_no_cmt) < len(rest_no_cmt):
        trailing_ws = rest_no_cmt[len(stripped_no_cmt) :]

    in_suffix = ""
    if stripped_no_cmt == "in":
        return line, False
    if stripped_no_cmt.endswith(" in") or stripped_no_cmt.endswith("\tin"):
        in_suffix = stripped_no_cmt[-3:]
        rest_body = stripped_no_cmt[:-3].rstrip()
    else:
        rest_body = stripped_no_cmt

    def _is_dropped_ns(tok: str) -> bool:
        if not tok:
            return False
        first_seg = tok.split(".", 1)[0]
        if first_seg in _PROTECTED_MATHLIB_TOP_NS:
            return False
        if tok in dropped_only_ns:
            return True
        if cur_ns_prefix and f"{cur_ns_prefix}.{tok}" in dropped_only_ns:
            return True
        if mod_dropped_open and f"{cur_ns_prefix}::{tok}" in mod_dropped_open:
            return True
        return False

    if "(" in rest_body or ")" in rest_body:
        m_paren = re.match(
            r"^\s*([A-Za-z0-9_'.\u0080-\uffff]+)\s*\([^()]*\)\s*$", rest_body
        )
        if m_paren and _is_dropped_ns(m_paren.group(1)):
            return None, True
        return line, False

    tokens = rest_body.split()
    if not tokens:
        return line, False
    kept_tokens = [t for t in tokens if not _is_dropped_ns(t)]
    if len(kept_tokens) == len(tokens):
        return line, False
    if not kept_tokens:
        return None, True
    rebuilt = f"{indent}{open_kw}{sp}{' '.join(kept_tokens)}{in_suffix}{trailing_ws}{comment_suffix}"
    return rebuilt, True


def transform_lean_source_full(
    source_text: str,
    *,
    module_id: int,
    plan: PrunePlan,
    decl_spans: list[tuple[int, int, int, bool]],
    strip_dead_decls: bool = True,
    rewrite_imports: bool = True,
    consolidation_ops: Sequence[ConsolidationOp] | None = None,
    strip_comments: bool = False,
    keep_docstrings: bool = False,
) -> TransformResult:
    """Apply all enabled source-level transformations to a single `.lean` module:
    1. Intra-module dead theorem/lemma stripping
    2. Verified in-scope exact-duplicate proof consolidation
    3. Dead-import removal, transitive barrel/external import splicing, & dead `open` cleanup
    4. Syntax-safe comment and redundant blank-line stripping
    """
    lines = source_text.splitlines()
    n_lines = len(lines)
    orig_nonblank = sum(1 for ln in lines if ln.strip())
    if n_lines == 0:
        return TransformResult(text=source_text)

    # 1. Compute 0-based line mask for dead intra-module theorems/lemmas
    if strip_dead_decls and decl_spans:
        strip_line_mask, stripped_decls = _compute_strip_line_mask(
            lines, decl_spans, plan.kept_decl_ids
        )
    else:
        strip_line_mask = bytearray(n_lines)
        stripped_decls = 0

    # 2. Apply verified in-scope exact-duplicate proof delegations (in reverse line order)
    consolidated_decls = 0
    consolidated_saved_loc = 0
    if consolidation_ops:
        lines, consolidated_decls, consolidated_saved_loc = apply_consolidations_to_lines(
            lines,
            consolidation_ops,
            strip_line_mask=strip_line_mask,
        )

    # Precompute external imports already transitively covered by surviving direct imports
    covered_ext: set[str] = set()
    if rewrite_imports:
        for idx, line in enumerate(lines):
            if strip_line_mask[idx]:
                continue
            m = _IMPORT_LINE_RE.match(line)
            if not m:
                continue
            imp_target = m.group(2)
            target_mid = plan.path_to_mid.get(imp_target) or plan.path_to_mid.get(
                _normalize_mod_name(imp_target)
            )
            if target_mid is None:
                covered_ext.add(imp_target)
            elif target_mid in plan.kept_modules:
                covered_ext.update(plan.trans_ext_imports.get(target_mid, ()))

    # 3. Rewrite / splice imports, clean dropped-only `open` namespaces, and emit surviving lines
    out_lines: list[str] = []
    seen_imports: set[str] = set()
    dropped_imports = 0
    rewritten_imports = 0
    self_mod_name = _normalize_mod_name(plan.mod_path.get(module_id, ""))
    stripped_nonblank_from_mask = 0
    ns_stack: list[tuple[str, str | None]] = []
    import_zone_out_idx: int | None = None

    for idx, line in enumerate(lines):
        if strip_line_mask[idx]:
            if line.strip():
                stripped_nonblank_from_mask += 1
            continue
        if rewrite_imports:
            m = _IMPORT_LINE_RE.match(line)
            if m:
                prefix, imp_target, suffix = m.group(1), m.group(2), m.group(3)
                target_mid = plan.path_to_mid.get(imp_target) or plan.path_to_mid.get(
                    _normalize_mod_name(imp_target)
                )
                if target_mid is None:
                    if imp_target not in seen_imports:
                        seen_imports.add(imp_target)
                        out_lines.append(line)
                    import_zone_out_idx = len(out_lines)
                    continue
                if target_mid in plan.kept_modules:
                    if imp_target not in seen_imports and imp_target != self_mod_name:
                        seen_imports.add(imp_target)
                        out_lines.append(line)
                    import_zone_out_idx = len(out_lines)
                    continue
                replacements = _replacement_imports_for_dropped(
                    module_id, target_mid, plan, covered_ext=covered_ext
                )
                added_any = False
                for rep in replacements:
                    if rep not in seen_imports and rep != self_mod_name:
                        seen_imports.add(rep)
                        out_lines.append(f"{prefix}{rep}{suffix}")
                        covered_ext.add(rep)
                        rep_mid = plan.path_to_mid.get(rep) or plan.path_to_mid.get(
                            _normalize_mod_name(rep)
                        )
                        if rep_mid is not None:
                            covered_ext.update(plan.trans_ext_imports.get(rep_mid, ()))
                        added_any = True
                if added_any:
                    rewritten_imports += 1
                else:
                    dropped_imports += 1
                import_zone_out_idx = len(out_lines)
                continue

            mod_dropped_open = plan.per_module_dropped_open_ns.get(module_id)
            if plan.dropped_only_namespaces or mod_dropped_open:
                cur_ns_prefix = ".".join(v for k, v in ns_stack if k == "ns" and v)
                rewritten_open, changed_open = _rewrite_open_line(
                    line, cur_ns_prefix, plan.dropped_only_namespaces, mod_dropped_open
                )
                if changed_open:
                    if rewritten_open is None:
                        continue
                    line = rewritten_open

        _update_scope_stack(ns_stack, line)
        out_lines.append(line)

    if rewrite_imports:
        missing_bridges: list[str] = []
        for dm in sorted(plan.needed_mod_bridges.get(module_id, ())):
            if dm in plan.mod_path:
                norm_dm = _normalize_mod_name(plan.mod_path[dm])
                if norm_dm and norm_dm != self_mod_name and norm_dm not in seen_imports:
                    seen_imports.add(norm_dm)
                    missing_bridges.append(f"import {norm_dm}")
        if missing_bridges:
            ins_at = import_zone_out_idx if import_zone_out_idx is not None else 0
            out_lines[ins_at:ins_at] = missing_bridges
            rewritten_imports += len(missing_bridges)

    text = "\n".join(out_lines)
    if source_text.endswith("\n") and text:
        text += "\n"

    # 4. Optional Lean-4-safe comment and redundant blank-line stripping
    stripped_comment_lines = 0
    if strip_comments:
        text, stripped_comment_lines = strip_lean_comments(text, keep_docstrings=keep_docstrings)

    final_lines_list = text.splitlines()
    final_total = len(final_lines_list)
    final_nonblank = sum(1 for ln in final_lines_list if ln.strip())

    return TransformResult(
        text=text,
        stripped_decls=stripped_decls,
        stripped_nonblank_lines=stripped_nonblank_from_mask + dropped_imports,
        dropped_imports=dropped_imports,
        rewritten_imports=rewritten_imports,
        consolidated_decls=consolidated_decls,
        consolidated_saved_loc=consolidated_saved_loc,
        stripped_comment_and_blank_lines=stripped_comment_lines,
        orig_total_lines=n_lines,
        orig_nonblank_lines=orig_nonblank,
        final_total_lines=final_total,
        final_nonblank_lines=final_nonblank,
    )


def transform_lean_source(
    source_text: str,
    *,
    module_id: int,
    plan: PrunePlan,
    decl_spans: list[tuple[int, int, int, bool]],
    strip_dead_decls: bool = True,
    rewrite_imports: bool = True,
    consolidation_ops: Sequence[ConsolidationOp] | None = None,
    strip_comments: bool = False,
    keep_docstrings: bool = False,
) -> tuple[str, int, int, int, int]:
    """Backwards-compatible 5-tuple wrapper around ``transform_lean_source_full``."""
    res = transform_lean_source_full(
        source_text,
        module_id=module_id,
        plan=plan,
        decl_spans=decl_spans,
        strip_dead_decls=strip_dead_decls,
        rewrite_imports=rewrite_imports,
        consolidation_ops=consolidation_ops,
        strip_comments=strip_comments,
        keep_docstrings=keep_docstrings,
    )
    return (
        res.text,
        res.stripped_decls,
        res.stripped_nonblank_lines,
        res.dropped_imports,
        res.rewritten_imports,
    )


# ---------------------------------------------------------------------------
# Zero-extraction archive streaming helpers
# ---------------------------------------------------------------------------


class _ConcatPartStream(io.RawIOBase):
    """Zero-disk-extraction sequential reader across concatenated `.tar.gz.part*` files."""

    def __init__(self, part_paths: Sequence[Path]) -> None:
        self._parts = list(part_paths)
        self._idx = 0
        self._fh = open(self._parts[0], "rb") if self._parts else None

    def readable(self) -> bool:
        return True

    def readinto(self, b: Any) -> int:
        if self._fh is None:
            return 0
        total = 0
        mv = memoryview(b)
        while total < len(mv) and self._fh is not None:
            n = self._fh.readinto(mv[total:])
            if n:
                total += n
            else:
                self._fh.close()
                self._idx += 1
                if self._idx < len(self._parts):
                    self._fh = open(self._parts[self._idx], "rb")
                else:
                    self._fh = None
        return total

    def close(self) -> None:
        if self._fh is not None:
            self._fh.close()
            self._fh = None
        super().close()


def _resolve_source_parts(source: str | Path | Sequence[str | Path]) -> tuple[str, list[Path]]:
    if isinstance(source, (list, tuple)):
        paths = [Path(p) for p in source]
        return "parts", paths
    s = str(source)
    if any(ch in s for ch in ("*", "?", "[")):
        matched = sorted(Path(p) for p in glob.glob(s))
        if not matched:
            raise FileNotFoundError(f"No files matched glob: {s}")
        return "parts", matched
    p = Path(s)
    if p.is_dir():
        return "dir", [p]
    if re.search(r"\.part\d+$", p.name):
        base = re.sub(r"\.part\d+$", ".part*", str(p))
        siblings = sorted(Path(x) for x in glob.glob(base))
        return "parts", siblings or [p]
    return "archive", [p]


def _iter_source_entries(
    source: str | Path | Sequence[str | Path],
) -> Iterator[tuple[str, bytes]]:
    kind, paths = _resolve_source_parts(source)
    if kind == "dir":
        root = paths[0]
        for fpath in sorted(root.rglob("*")):
            if not fpath.is_file():
                continue
            rel = fpath.relative_to(root).as_posix()
            if rel.startswith(".lake/") or "/.lake/" in rel or rel.startswith(".git/"):
                continue
            if fpath.name in _CONFIG_FILENAMES or fpath.suffix == ".lean":
                yield rel, fpath.read_bytes()
        return

    raw_stream = _ConcatPartStream(paths)
    buf_stream = io.BufferedReader(raw_stream, buffer_size=1 << 20)
    try:
        with tarfile.open(fileobj=buf_stream, mode="r|*") as tf:
            for member in tf:
                if not member.isfile():
                    continue
                name = member.name.lstrip("./")
                base = name.rsplit("/", 1)[-1]
                if base in _CONFIG_FILENAMES or name.endswith(".lean"):
                    extracted = tf.extractfile(member)
                    if extracted is not None:
                        yield name, extracted.read()
    except (tarfile.ReadError, zlib.error, EOFError):
        pass
    finally:
        buf_stream.close()


def _strip_archive_root_prefix(rel_path: str) -> str:
    norm = rel_path.replace("\\", "/").lstrip("./")
    if norm.startswith("lean/"):
        return norm[5:]
    return norm


def _write_bytes_to_tar(tf: tarfile.TarFile, arcname: str, data: bytes, mtime: int) -> None:
    info = tarfile.TarInfo(name=arcname)
    info.size = len(data)
    info.mtime = mtime
    info.mode = 0o644
    tf.addfile(info, io.BytesIO(data))


# ---------------------------------------------------------------------------
# Main multi-pass project materialization & streaming archive emitter
# ---------------------------------------------------------------------------


def _compute_per_module_dropped_open_ns(
    plan: PrunePlan,
    ctx: _PruneGraphContext,
    raw_by_mid: dict[int, bytes],
    *,
    strip_dead_decls: bool = True,
) -> dict[int, frozenset[str]]:
    """Identify dotted project namespaces in ``open ...`` lines that are NOT defined in
    each caller module's own surviving file or kept transitive import closure.
    """
    dropped_barrels = (
        ctx.all_zero_decl_mods - plan.kept_modules
    ) | plan.collapsed_barrel_modules
    barrel_memo: dict[int, tuple[int, ...]] = {}

    def _spliced_from_barrel(bmid: int) -> tuple[int, ...]:
        if bmid in barrel_memo:
            return barrel_memo[bmid]
        visited: set[int] = {bmid}
        q: deque[int] = deque([bmid])
        found: list[int] = []
        while q:
            cur = q.popleft()
            for nb in plan.mod_imports.get(cur, ()):
                if nb in visited:
                    continue
                visited.add(nb)
                if nb in plan.kept_modules:
                    found.append(nb)
                elif nb in dropped_barrels:
                    q.append(nb)
        res = tuple(found)
        barrel_memo[bmid] = res
        return res

    eff_imps: dict[int, list[int]] = {}
    for m in plan.kept_modules:
        seen: set[int] = set()
        adj_m: list[int] = []
        for nb in plan.mod_imports.get(m, ()):
            if nb in plan.kept_modules and nb != m and nb not in seen:
                seen.add(nb)
                adj_m.append(nb)
            elif nb in dropped_barrels:
                for km in _spliced_from_barrel(nb):
                    if km != m and km not in seen:
                        seen.add(km)
                        adj_m.append(km)
        for bm in plan.needed_mod_bridges.get(m, ()):
            if bm in plan.kept_modules and bm != m and bm not in seen:
                seen.add(bm)
                adj_m.append(bm)
        eff_imps[m] = adj_m

    # Post-order over effective kept DAG
    state: dict[int, int] = {}
    post_order: list[int] = []
    for start in sorted(plan.kept_modules):
        if state.get(start, 0) != 0:
            continue
        stack: list[tuple[int, int]] = [(start, 0)]
        state[start] = 1
        while stack:
            node, idx = stack[-1]
            nbs = eff_imps.get(node, ())
            if idx < len(nbs):
                stack[-1] = (node, idx + 1)
                nb = nbs[idx]
                if state.get(nb, 0) == 0:
                    state[nb] = 1
                    stack.append((nb, 0))
            else:
                stack.pop()
                state[node] = 2
                post_order.append(node)

    mod_own_ns: dict[int, set[str]] = defaultdict(set)
    for did in plan.kept_decl_ids:
        dm = ctx.decl_mod.get(did)
        if dm is not None and dm in plan.kept_modules:
            _add_ns_prefixes(mod_own_ns[dm], ctx.decl_name.get(did, ""))

    open_queries: dict[int, list[tuple[str, str, list[str]]]] = {}
    all_cands: set[str] = set()

    def _candidates(tok: str, cur_ns: str) -> list[str]:
        cands = [tok]
        if cur_ns:
            parts = cur_ns.split(".")
            for i in range(len(parts), 0, -1):
                cands.append(".".join(parts[:i]) + "." + tok)
        return cands

    for mid in plan.kept_modules:
        rb = raw_by_mid.get(mid)
        if not rb:
            continue
        has_ns = b"namespace" in rb
        has_open = b"open" in rb
        if not has_ns and not has_open:
            continue

        src_text = rb.decode("utf-8", errors="replace")
        lines = src_text.splitlines()
        spans = ctx.spans_by_mod.get(mid, [])
        if strip_dead_decls and spans:
            mask, _ = _compute_strip_line_mask(lines, spans, plan.kept_decl_ids)
            surv_lines = [ln for i, ln in enumerate(lines) if not mask[i]]
        else:
            surv_lines = lines

        if has_ns:
            ns_set = _collect_declared_namespaces("\n".join(surv_lines))
            if ns_set:
                mod_own_ns[mid].update(ns_set)

        if has_open:
            ns_stack: list[tuple[str, str | None]] = []
            q_list: list[tuple[str, str, list[str]]] = []
            for ln in surv_lines:
                om = _NAMESPACE_OPEN_LINE_RE.match(ln)
                if om:
                    rest = om.group(4).split("--", 1)[0].rstrip()
                    if rest.endswith(" in") or rest.endswith("\tin"):
                        rest = rest[:-3].rstrip()
                    if "(" not in rest and ")" not in rest:
                        cur_ns = ".".join(v for k, v in ns_stack if k == "ns" and v)
                        for tok in rest.split():
                            if "." not in tok:
                                continue
                            first_seg = tok.split(".", 1)[0]
                            if first_seg in _PROTECTED_MATHLIB_TOP_NS:
                                continue
                            if tok in plan.dropped_only_namespaces:
                                continue
                            cs = _candidates(tok, cur_ns)
                            if any(c in ctx.all_proj_ns for c in cs):
                                q_list.append((tok, cur_ns, cs))
                                all_cands.update(cs)
                _update_scope_stack(ns_stack, ln)
            if q_list:
                open_queries[mid] = q_list

    if not open_queries:
        return {}

    present_cands: set[str] = set()
    for s in mod_own_ns.values():
        present_cands.update(s & all_cands)

    ok_map: dict[int, list[bool]] = {m: [False] * len(ql) for m, ql in open_queries.items()}
    cand_list = sorted(present_cands)
    for off in range(0, len(cand_list), 4096):
        chunk = cand_list[off : off + 4096]
        cbit = {c: 1 << i for i, c in enumerate(chunk)}
        trans: dict[int, int] = {}
        for u in post_order:
            b = 0
            for ns in mod_own_ns.get(u, ()):
                if ns in cbit:
                    b |= cbit[ns]
            for v in eff_imps.get(u, ()):
                b |= trans.get(v, 0)
            trans[u] = b
        for mid, ql in open_queries.items():
            tb = trans.get(mid, 0)
            ok_flags = ok_map[mid]
            for idx, (_, _, cs) in enumerate(ql):
                if not ok_flags[idx]:
                    if any(tb & cbit.get(c, 0) for c in cs):
                        ok_flags[idx] = True

    result: dict[int, frozenset[str]] = {}
    for mid, ql in open_queries.items():
        bad_keys = {
            f"{cur_ns}::{tok}"
            for (tok, cur_ns, _), is_ok in zip(ql, ok_map[mid])
            if not is_ok
        }
        if bad_keys:
            result[mid] = frozenset(bad_keys)
    return result


_IDENT_TOKEN_RE = re.compile(
    r"[A-Za-z_\u00c0-\u024f\u0370-\u03ff][A-Za-z0-9_'\u0080-\uffff]*"
)
_DOT_SUFFIX_RE = re.compile(
    r"\.([A-Za-z_\u00c0-\u024f\u0370-\u03ff][A-Za-z0-9_'\u0080-\uffff]*)"
)


def _run_root_dot_fixpoint(
    plan: PrunePlan,
    ctx: _PruneGraphContext,
    raw_by_mid: dict[int, bytes],
    *,
    strip_dead_decls: bool = True,
) -> bool:
    """Iteratively resolve ``_root_.<Decl>``, intra-module, and dot-projection references
    in surviving lines of ``kept_modules``.

    Expands ``kept_decl_ids`` and ``kept_modules`` to a fixpoint and records cross-module edges
    in ``ctx.extra_mod_edges``. Returns True if any new declarations or modules were added.
    """
    name_to_dids: dict[str, list[int]] = defaultdict(list)
    for did, nm in ctx.decl_name.items():
        if nm:
            name_to_dids[nm].append(did)

    scanned_root_cnt: dict[int, int] = {}
    scanned_rescue_cnt: dict[int, int] = {}
    dot_tokens_seen: set[str] = set()
    changed_any = False

    def _expand_and_verify_barrels(seeds: Sequence[int]) -> None:
        _expand_instance_aware_closure(plan, ctx, seeds)
        if plan.collapse_barrels and plan.collapsed_barrel_modules:
            restored: set[int] = set()
            for bmid in list(plan.collapsed_barrel_modules):
                rb = raw_by_mid.get(bmid)
                if rb is not None and not is_pure_import_barrel_source(
                    rb.decode("utf-8", errors="replace")
                ):
                    restored.add(bmid)
            if restored:
                ctx.restored_non_pure_barrels |= restored
                plan.collapsed_barrel_modules -= restored
                plan.kept_modules |= restored
                plan.dropped_modules -= restored

    while True:
        # Phase 1: fast _root_.<Decl> closure (only inspects modules containing `_root_.`)
        while True:
            new_seeds: list[int] = []
            seen_seed_set: set[int] = set()

            for mid in sorted(plan.kept_modules):
                raw_bytes = raw_by_mid.get(mid)
                if not raw_bytes or b"_root_." not in raw_bytes:
                    continue
                cur_kept_cnt = sum(
                    1 for d in ctx.mod_to_decls.get(mid, ()) if d in plan.kept_decl_ids
                )
                if scanned_root_cnt.get(mid) == cur_kept_cnt:
                    continue
                scanned_root_cnt[mid] = cur_kept_cnt

                src_text = raw_bytes.decode("utf-8", errors="replace")
                lines = src_text.splitlines()
                spans = ctx.spans_by_mod.get(mid, [])
                if strip_dead_decls and spans:
                    mask, _ = _compute_strip_line_mask(lines, spans, plan.kept_decl_ids)
                    surviving_text = "\n".join(ln for i, ln in enumerate(lines) if not mask[i])
                else:
                    surviving_text = src_text

                clean_text, _ = strip_lean_comments(surviving_text, keep_docstrings=False)
                for m_ref in _ROOT_DOT_REF_RE.finditer(clean_text):
                    target_name = m_ref.group(1)
                    dids = name_to_dids.get(target_name)
                    if not dids and "." in target_name:
                        parent = target_name.rsplit(".", 1)[0]
                        pdids = name_to_dids.get(parent)
                        if pdids:
                            dids = [
                                d
                                for d in pdids
                                if ctx.decl_kind.get(d) in {"structure", "inductive", "class"}
                            ]
                    if not dids:
                        continue
                    for dst_id in dids:
                        dm = ctx.decl_mod.get(dst_id)
                        if dm is not None and dm != mid and dm in ctx.project_mids:
                            ctx.extra_mod_edges[mid].add(dm)
                        if dst_id not in plan.kept_decl_ids and dst_id not in seen_seed_set:
                            seen_seed_set.add(dst_id)
                            new_seeds.append(dst_id)

            if not new_seeds:
                break

            changed_any = True
            _expand_and_verify_barrels(new_seeds)

        # Phase 2: intra-module short-name rescue & kept-type dot-projection lemma rescue
        kept_type_ns: set[str] = {
            ctx.decl_name[d]
            for d in plan.kept_decl_ids
            if ctx.decl_kind.get(d) in {"structure", "class", "inductive", "def", "abbrev"}
            and ctx.decl_name.get(d)
        }
        dot_candidates: dict[str, list[int]] = defaultdict(list)
        for dlist in plan.strippable_decl_ids_by_mod.values():
            for d in dlist:
                nm = ctx.decl_name.get(d, "")
                if "." not in nm:
                    continue
                parent, short = nm.rsplit(".", 1)
                if len(short) >= 3 and parent in kept_type_ns:
                    dot_candidates[short].append(d)

        rescue_seeds: list[int] = []
        seen_rescue: set[int] = set()

        for mid in sorted(plan.kept_modules):
            raw_bytes = raw_by_mid.get(mid)
            if not raw_bytes:
                continue
            cur_kept_cnt = sum(
                1 for d in ctx.mod_to_decls.get(mid, ()) if d in plan.kept_decl_ids
            )
            if scanned_rescue_cnt.get(mid) == cur_kept_cnt:
                continue
            scanned_rescue_cnt[mid] = cur_kept_cnt

            st_list = plan.strippable_decl_ids_by_mod.get(mid, ())
            if not st_list and not dot_candidates:
                continue

            src_text = raw_bytes.decode("utf-8", errors="replace")
            lines = src_text.splitlines()
            spans = ctx.spans_by_mod.get(mid, [])
            if strip_dead_decls and spans:
                mask, _ = _compute_strip_line_mask(lines, spans, plan.kept_decl_ids)
                surviving_text = "\n".join(ln for i, ln in enumerate(lines) if not mask[i])
            else:
                surviving_text = src_text

            clean_text, _ = strip_lean_comments(surviving_text, keep_docstrings=False)
            if st_list:
                toks = set(_IDENT_TOKEN_RE.findall(clean_text))
                for d in st_list:
                    sh = ctx.decl_name.get(d, "").rsplit(".", 1)[-1]
                    if sh and sh in toks and d not in seen_rescue:
                        seen_rescue.add(d)
                        rescue_seeds.append(d)
            if dot_candidates:
                dot_tokens_seen.update(_DOT_SUFFIX_RE.findall(clean_text))

        if dot_candidates and dot_tokens_seen:
            for sh, dlist in dot_candidates.items():
                if sh in dot_tokens_seen:
                    for d in dlist:
                        if d not in seen_rescue:
                            seen_rescue.add(d)
                            rescue_seeds.append(d)

        if not rescue_seeds:
            break

        changed_any = True
        _expand_and_verify_barrels(rescue_seeds)

    return changed_any


def materialize_project(
    db: sqlite3.Connection | str | Path,
    *,
    source: str | Path | Sequence[str | Path] | None = None,
    output_dir: str | Path | None = None,
    output_archive: str | Path | None = None,
    roots: Sequence[str] | None = None,
    mode: str = "instance-aware",
    strip_dead_decls: bool = True,
    rewrite_imports: bool = True,
    collapse_barrels: bool = False,
    consolidate_duplicates: bool = False,
    strip_comments: bool = False,
    keep_docstrings: bool = False,
    merge_modules: bool = False,
    target_module_loc: int = 1400,
    allow_cross_bundle_consolidation: bool = True,
    dry_run: bool = False,
    max_files: int | None = None,
) -> MaterializeReport:
    """Compute pruning + consolidation plan and stream-materialize a compressed Lean 4 project
    to a directory (``output_dir``) and/or directly into a ``.tar.gz`` archive (``output_archive``)
    with zero intermediate disk unpacking.
    """
    conn, should_close = _open_db(db)
    try:
        plan, report, ctx = _compute_prune_plan_with_ctx(
            conn,
            roots=roots,
            mode=mode,
            collapse_barrels=collapse_barrels,
        )

        has_output_target = (output_dir is not None) or (output_archive is not None)
        cplan: ConsolidationPlan | None = None
        if dry_run or source is None or not has_output_target:
            if consolidate_duplicates:
                cplan = plan_consolidation(conn, plan)
                report.hoistable_duplicate_groups = cplan.report.hoistable_groups
                report.hoistable_redundant_decls = cplan.report.hoistable_redundant_decls
                report.hoistable_estimated_saved_loc = cplan.report.hoistable_estimated_saved_loc
                report.consolidated_duplicates = cplan.report.in_scope_candidates
                report.consolidated_saved_loc = cplan.report.in_scope_estimated_saved_loc
            try:
                set_meta(conn, f"analysis_materialize_{mode}", json.dumps(report.to_dict()))
                conn.commit()
            except sqlite3.OperationalError:
                pass
            return report

        # Measure raw archive byte size if input is archive/parts
        src_kind, src_paths = _resolve_source_parts(source)
        if src_kind in ("parts", "archive"):
            report.raw_archive_bytes = sum(p.stat().st_size for p in src_paths if p.exists())

        total_raw_uncompressed_bytes = 0
        raw_entries: list[tuple[str, bytes]] | None = None
        raw_by_mid: dict[int, bytes] = {}

        if max_files is None:
            raw_entries = []
            for rel_path, raw_bytes in _iter_source_entries(source):
                total_raw_uncompressed_bytes += len(raw_bytes)
                clean_rel = _strip_archive_root_prefix(rel_path)
                base_name = clean_rel.rsplit("/", 1)[-1]
                is_cfg = base_name in _CONFIG_FILENAMES and "/" not in clean_rel
                if is_cfg or clean_rel.endswith(".lean"):
                    raw_entries.append((rel_path, raw_bytes))
                    if not is_cfg:
                        mod_key = _normalize_mod_name(clean_rel)
                        mid = (
                            plan.path_to_mid.get(clean_rel)
                            or plan.path_to_mid.get(mod_key)
                            or plan.path_to_mid.get(rel_path)
                        )
                        if mid is not None:
                            raw_by_mid[mid] = raw_bytes

            # 1. Verify every collapsed barrel is strictly import-only in actual source
            barrels_restored = False
            if collapse_barrels and plan.collapsed_barrel_modules:
                restored: set[int] = set()
                for bmid in list(plan.collapsed_barrel_modules):
                    rb = raw_by_mid.get(bmid)
                    if rb is not None and not is_pure_import_barrel_source(
                        rb.decode("utf-8", errors="replace")
                    ):
                        restored.add(bmid)
                if restored:
                    barrels_restored = True
                    ctx.restored_non_pure_barrels |= restored
                    plan.collapsed_barrel_modules -= restored
                    plan.kept_modules |= restored
                    plan.dropped_modules -= restored

            # 2. Gap 2 fix: iterative _root_.<Decl> closure in instance-aware mode
            fix2_changed = False
            if mode == "instance-aware":
                fix2_changed = _run_root_dot_fixpoint(
                    plan,
                    ctx,
                    raw_by_mid,
                    strip_dead_decls=strip_dead_decls,
                )

            # Collect explicit `namespace` declarations from kept modules so zero-decl
            # syntax/notation namespaces are never mistakenly stripped from `open`.
            for m in plan.kept_modules:
                rb = raw_by_mid.get(m)
                if rb and b"namespace" in rb:
                    ctx.extra_kept_ns.update(
                        _collect_declared_namespaces(rb.decode("utf-8", errors="replace"))
                    )

            if barrels_restored or fix2_changed or ctx.extra_kept_ns:
                _sync_report_from_plan(report, plan, ctx)
                _finalize_bridges_and_namespaces(plan, ctx)

            if rewrite_imports:
                plan.per_module_dropped_open_ns = _compute_per_module_dropped_open_ns(
                    plan,
                    ctx,
                    raw_by_mid,
                    strip_dead_decls=strip_dead_decls,
                )

            if consolidate_duplicates:
                cplan = plan_consolidation(conn, plan)
                report.hoistable_duplicate_groups = cplan.report.hoistable_groups
                report.hoistable_redundant_decls = cplan.report.hoistable_redundant_decls
                report.hoistable_estimated_saved_loc = cplan.report.hoistable_estimated_saved_loc
                report.consolidated_duplicates = cplan.report.in_scope_candidates
                report.consolidated_saved_loc = cplan.report.in_scope_estimated_saved_loc
                need_cplan_mids = cplan.canon_mods_needed | cplan.dup_mods_needed
                if need_cplan_mids:
                    cplan_sources = {
                        mid: raw_by_mid[mid].decode("utf-8", errors="replace")
                        for mid in need_cplan_mids
                        if mid in raw_by_mid
                    }
                    verify_consolidation_plan_with_sources(cplan, cplan_sources)
        else:
            if consolidate_duplicates:
                cplan = plan_consolidation(conn, plan)
                report.hoistable_duplicate_groups = cplan.report.hoistable_groups
                report.hoistable_redundant_decls = cplan.report.hoistable_redundant_decls
                report.hoistable_estimated_saved_loc = cplan.report.hoistable_estimated_saved_loc
                report.consolidated_duplicates = cplan.report.in_scope_candidates
                report.consolidated_saved_loc = cplan.report.in_scope_estimated_saved_loc

            need_prescan_mids: set[int] = set()
            if cplan is not None:
                need_prescan_mids |= cplan.canon_mods_needed | cplan.dup_mods_needed
            if collapse_barrels and plan.collapsed_barrel_modules:
                need_prescan_mids |= plan.collapsed_barrel_modules

            if need_prescan_mids:
                prescan_sources: dict[int, str] = {}
                for rel_path, raw_bytes in _iter_source_entries(source):
                    clean_rel = _strip_archive_root_prefix(rel_path)
                    if not clean_rel.endswith(".lean"):
                        continue
                    mod_key = _normalize_mod_name(clean_rel)
                    mid = (
                        plan.path_to_mid.get(clean_rel)
                        or plan.path_to_mid.get(mod_key)
                        or plan.path_to_mid.get(rel_path)
                    )
                    if mid is not None and mid in need_prescan_mids:
                        prescan_sources[mid] = raw_bytes.decode("utf-8", errors="replace")

                if collapse_barrels and plan.collapsed_barrel_modules:
                    restored_mf: set[int] = set()
                    for bmid in list(plan.collapsed_barrel_modules):
                        bsrc = prescan_sources.get(bmid)
                        if bsrc is not None and not is_pure_import_barrel_source(bsrc):
                            restored_mf.add(bmid)
                    if restored_mf:
                        ctx.restored_non_pure_barrels |= restored_mf
                        plan.collapsed_barrel_modules -= restored_mf
                        plan.kept_modules |= restored_mf
                        plan.dropped_modules -= restored_mf
                        _sync_report_from_plan(report, plan, ctx)
                        _finalize_bridges_and_namespaces(plan, ctx)

                if cplan is not None:
                    verify_consolidation_plan_with_sources(cplan, prescan_sources)

        out_root: Path | None = None
        if output_dir is not None:
            out_root = Path(output_dir)
            out_root.mkdir(parents=True, exist_ok=True)
            report.output_dir = str(out_root)

        archive_path: Path | None = None
        tar_fh: tarfile.TarFile | None = None
        if output_archive is not None:
            archive_path = Path(output_archive)
            archive_path.parent.mkdir(parents=True, exist_ok=True)
            report.output_archive = str(archive_path)
            tar_fh = tarfile.open(archive_path, mode="w:gz", compresslevel=6)

        spans_by_mod = ctx.spans_by_mod

        files_written = 0
        configs_copied = 0
        total_stripped_lines = 0
        total_stripped_decls = 0
        total_dropped_imps = 0
        total_rewritten_imps = 0
        total_consolidated_decls = 0
        total_consolidated_saved_loc = 0
        total_stripped_comment_lines = 0
        total_final_nonblank_loc = 0
        total_final_lines = 0
        total_compressed_uncompressed_bytes = 0
        seen_lean = 0
        now_mtime = int(time.time())
        staged_modules: dict[str, tuple[str, str]] = {}
        staged_configs: dict[str, bytes] = {}
        merge_rep: MergeReport | None = None

        entry_iter = (
            iter(raw_entries) if raw_entries is not None else _iter_source_entries(source)
        )
        try:
            for rel_path, raw_bytes in entry_iter:
                if raw_entries is None:
                    total_raw_uncompressed_bytes += len(raw_bytes)
                clean_rel = _strip_archive_root_prefix(rel_path)
                base_name = clean_rel.rsplit("/", 1)[-1]

                if base_name in _CONFIG_FILENAMES and "/" not in clean_rel:
                    if merge_modules:
                        staged_configs[clean_rel] = raw_bytes
                    else:
                        if out_root is not None:
                            dest = out_root / clean_rel
                            dest.parent.mkdir(parents=True, exist_ok=True)
                            dest.write_bytes(raw_bytes)
                        if tar_fh is not None:
                            _write_bytes_to_tar(tar_fh, clean_rel, raw_bytes, now_mtime)
                        total_compressed_uncompressed_bytes += len(raw_bytes)
                    configs_copied += 1
                    continue

                if not clean_rel.endswith(".lean"):
                    continue

                seen_lean += 1
                if max_files is not None and seen_lean > max_files:
                    break

                mod_key = _normalize_mod_name(clean_rel)
                mid = (
                    plan.path_to_mid.get(clean_rel)
                    or plan.path_to_mid.get(mod_key)
                    or plan.path_to_mid.get(rel_path)
                )
                if mid is None or mid not in plan.kept_modules:
                    continue

                src_text = raw_bytes.decode("utf-8", errors="replace")
                mod_ops = cplan.ops_by_mod.get(mid) if cplan is not None else None
                res = transform_lean_source_full(
                    src_text,
                    module_id=mid,
                    plan=plan,
                    decl_spans=spans_by_mod.get(mid, []),
                    strip_dead_decls=strip_dead_decls,
                    rewrite_imports=rewrite_imports,
                    consolidation_ops=mod_ops,
                    strip_comments=strip_comments,
                    keep_docstrings=keep_docstrings,
                )

                if merge_modules:
                    staged_modules[mod_key] = (clean_rel, res.text)
                else:
                    out_bytes = res.text.encode("utf-8")
                    if out_root is not None:
                        dest = out_root / clean_rel
                        dest.parent.mkdir(parents=True, exist_ok=True)
                        dest.write_bytes(out_bytes)
                    if tar_fh is not None:
                        _write_bytes_to_tar(tar_fh, clean_rel, out_bytes, now_mtime)
                    files_written += 1
                    total_final_nonblank_loc += res.final_nonblank_lines
                    total_final_lines += res.final_total_lines
                    total_compressed_uncompressed_bytes += len(out_bytes)

                total_stripped_lines += res.stripped_nonblank_lines
                total_stripped_decls += res.stripped_decls
                total_dropped_imps += res.dropped_imports
                total_rewritten_imps += res.rewritten_imports
                total_consolidated_decls += res.consolidated_decls
                total_consolidated_saved_loc += res.consolidated_saved_loc
                total_stripped_comment_lines += res.stripped_comment_and_blank_lines

            if raw_entries is not None:
                raw_entries.clear()
            raw_by_mid.clear()

            if merge_modules and staged_modules:
                lakefile_txt = (
                    staged_configs["lakefile.toml"].decode("utf-8", errors="replace")
                    if "lakefile.toml" in staged_configs
                    else None
                )
                root_mod_names = {
                    _normalize_mod_name(plan.mod_path[m])
                    for m in plan.root_module_ids
                    if m in plan.mod_path
                } | {"Main", "Statements"}
                merged_files, merge_rep = merge_project_modules(
                    staged_modules,
                    target_module_loc=target_module_loc,
                    lakefile_toml_text=lakefile_txt,
                    root_modules=sorted(root_mod_names),
                    conn=conn,
                    plan=plan,
                    consolidate_duplicates=consolidate_duplicates,
                    allow_cross_bundle_consolidation=allow_cross_bundle_consolidation,
                )
                for cfg_rel, cfg_bytes in staged_configs.items():
                    if out_root is not None:
                        dest = out_root / cfg_rel
                        dest.parent.mkdir(parents=True, exist_ok=True)
                        dest.write_bytes(cfg_bytes)
                    if tar_fh is not None:
                        _write_bytes_to_tar(tar_fh, cfg_rel, cfg_bytes, now_mtime)
                    total_compressed_uncompressed_bytes += len(cfg_bytes)

                for _, (bundle_rel, bundle_text) in merged_files.items():
                    out_bytes = bundle_text.encode("utf-8")
                    if out_root is not None:
                        dest = out_root / bundle_rel
                        dest.parent.mkdir(parents=True, exist_ok=True)
                        dest.write_bytes(out_bytes)
                    if tar_fh is not None:
                        _write_bytes_to_tar(tar_fh, bundle_rel, out_bytes, now_mtime)
                    files_written += 1
                    total_compressed_uncompressed_bytes += len(out_bytes)

                total_final_nonblank_loc = merge_rep.output_nonblank_loc
                total_final_lines = merge_rep.output_total_lines
                total_consolidated_decls += merge_rep.phase_b_total_consolidations
                total_consolidated_saved_loc += merge_rep.phase_b_saved_loc
        finally:
            if tar_fh is not None:
                tar_fh.close()

        if archive_path is not None and archive_path.exists():
            report.output_archive_bytes = archive_path.stat().st_size

        report.raw_uncompressed_bytes = total_raw_uncompressed_bytes
        report.compressed_uncompressed_bytes = total_compressed_uncompressed_bytes

        if files_written > 0:
            report.files_written = files_written
            report.config_files_copied = configs_copied
            report.intra_module_stripped_loc = total_stripped_lines
            report.stripped_intra_module_declarations = total_stripped_decls
            report.dropped_import_lines = total_dropped_imps
            report.rewritten_import_lines = total_rewritten_imps
            report.consolidated_duplicates = total_consolidated_decls
            report.consolidated_saved_loc = total_consolidated_saved_loc
            report.stripped_comment_and_blank_lines = total_stripped_comment_lines
            report.final_nonblank_loc = total_final_nonblank_loc
            report.final_total_lines = total_final_lines
            report.materialized_loc = total_final_nonblank_loc
            report.total_loc_reduction_pct = _pct(
                report.raw_loc - report.materialized_loc,
                report.raw_loc,
            )

        if cplan is not None:
            cplan.report.applied_consolidations = total_consolidated_decls
            cplan.report.applied_saved_loc = total_consolidated_saved_loc

        if merge_rep is not None:
            report.merge_modules_enabled = True
            report.target_module_loc = merge_rep.target_module_loc
            report.pre_merge_modules = merge_rep.input_modules
            report.merged_output_modules = merge_rep.output_modules
            report.eliminated_import_lines_by_merge = merge_rep.eliminated_import_lines
            report.loc_saved_by_merge = merge_rep.loc_saved_by_merge
            report.phase_b_consolidations = merge_rep.phase_b_total_consolidations
            report.phase_b_saved_loc = merge_rep.phase_b_saved_loc
            report.merge_dangling_imports = merge_rep.dangling_imports
            report.merge_cycle_count = merge_rep.cycle_count
            report.kept_modules = merge_rep.output_modules
            report.dropped_modules = max(0, report.raw_modules - merge_rep.output_modules)
            report.module_reduction_pct = _pct(report.dropped_modules, report.raw_modules)

        try:
            set_meta(conn, f"analysis_materialize_{mode}", json.dumps(report.to_dict()))
            if cplan is not None:
                set_meta(conn, "analysis_consolidation", json.dumps(cplan.report.to_dict()))
            if merge_rep is not None:
                set_meta(conn, "analysis_merge_modules", json.dumps(merge_rep.to_dict()))
            conn.commit()
        except sqlite3.OperationalError:
            pass
        return report
    finally:
        if should_close:
            conn.close()
