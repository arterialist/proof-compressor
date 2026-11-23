"""Stage 4 kernel-gated Lean 4 proof simplifier.

Implements rule-based and automation-assisted Lean 4 proof simplification
integrated directly with :func:`proof_compressor.refactor.gate.verify_refactor_gate`:

1. **Unused hypothesis & local `have`/`let`/`set` pruning** (plus dead `private` helpers).
2. **Tactic collapse & automation lifting** (`have := ...; exact this`, `first | ...`,
   `:= by exact ...`, consecutive `rw` merging, `calc` / sub-proof lifting to
   `omega`, `linarith`, `nlinarith`, `ring`, `positivity`, `norm_num`, `simp_all`,
   `aesop`, `grind`, `decide`).
3. **Mathlib absorption** (replacing bespoke `private` helpers that duplicate
   Mathlib theorems, plus single-use private helper inlining).
4. **Transactional kernel-gated acceptance** via ``lake build`` + verbatim
   ``#check`` type preservation + ``#print axioms`` check + strict effective LOC
   reduction, with automatic revert on any gate failure.
"""

from __future__ import annotations

import hashlib
import os
import re
import sqlite3
import tempfile
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Sequence

from proof_compressor.ingest.lean_parser import (
    ParsedDecl,
    canonical_type_hash,
    canonicalize_type,
    parse_lean_source,
)
from proof_compressor.refactor.gate import (
    STANDARD_LEAN_AXIOMS,
    CommandRunner,
    GateResult,
    count_effective_loc,
    find_lake_binary,
    parse_check_signatures,
    parse_print_axioms,
    run_subprocess_clean,
    verify_refactor_gate,
)

# Kept as module-level aliases for existing callers/tests; the gate now parses primed
# names and kills process groups itself.
_parse_print_axioms_safe = parse_print_axioms
_run_subprocess_clean = run_subprocess_clean

# Tactics that inspect the local context implicitly; if present later in the
# same scope, dropping a `have`/`let` still requires kernel verification.
_CONTEXT_TACTICS_RE = re.compile(
    r"\b(?:assumption|simp_all|aesop|omega|linarith|nlinarith|grind|tauto|"
    r"positivity|contradiction|trivial|decide)\b"
)

_DECL_EXPORT_KINDS = frozenset(
    {"theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "opaque"}
)

# Curated Mathlib theorems that frequently get re-proved as private helpers.
# Each entry maps a canonicalized signature regex to (mathlib_name, note).
_MATHLIB_CANONICAL_PATTERNS: tuple[tuple[re.Pattern[str], str, str], ...] = (
    (
        re.compile(r"WithZero\s*\(\s*Multiplicative ℤ\s*\).*≠\s*0.*\*.*≤.*\*.*:.*≤"),
        "le_of_mul_le_mul_right",
        "Right-cancellation for ordered group with zero (`WithZero (Multiplicative ℤ)`)",
    ),
    (
        re.compile(r"\(0\s*<\s*[^)]+\).*≤.*→.*≤.*/"),
        "le_div_iff₀",
        "Division inequality rearrangement (`le_div_iff₀`)",
    ),
    (
        re.compile(r"0\s*<.*→.*≤\s*1\s*↔.*≤"),
        "div_le_one",
        "Ratio `≤ 1` characterization (`div_le_one`)",
    ),
    (
        re.compile(r"∏[^,]+,.*=\s*1"),
        "Finset.prod_eq_one",
        "Product of ones (`Finset.prod_eq_one`)",
    ),
    (
        re.compile(r"∑[^,]+,.*=\s*0"),
        "Finset.sum_eq_zero",
        "Sum of zeros (`Finset.sum_eq_zero`)",
    ),
)

_IDENT_CHAR = r"A-Za-z0-9_'\u2080-\u2089"
_HAVE_LINE_RE = re.compile(
    rf"^(\s*)(have|let|set)\s+([A-Za-z_][{_IDENT_CHAR}]*)(?![{_IDENT_CHAR}])(.*)$"
)
_ANON_HAVE_RE = re.compile(r"^(\s*)have\s*:=\s*(.+)$")
_EXACT_IDENT_RE = re.compile(
    rf"^(\s*)exact\s+([A-Za-z_][{_IDENT_CHAR}]*)\s*$"
)
_SIMPA_USING_IDENT_RE = re.compile(
    rf"^(\s*)(simpa(?:\s+only)?(?:\s*\[[^\]]*\])?\s+using)\s+([A-Za-z_][{_IDENT_CHAR}]*)\s*$"
)
_RW_SINGLE_RE = re.compile(r"^(\s*)rw\s+\[([^\]]+)\]\s*$")
_FIRST_HEADER_RE = re.compile(r"^(\s*)first\s*$")
_FIRST_BRANCH_RE = re.compile(r"^(\s*)\|\s*(.+)$")
_BY_TAIL_RE = re.compile(r"^(\s*):?=\s*by\s*$")
_SET_WITH_RE = re.compile(
    rf"^(\s*set\s+[A-Za-z_][{_IDENT_CHAR}]*(?:\s*:[^:=]+)?\s*:=\s*.+?)\s+with\s+([A-Za-z_][{_IDENT_CHAR}]*)\s*$"
)


@dataclass
class SimplifyCandidate:
    """A single candidate source-level proof simplification rewrite."""

    rule: str
    description: str
    new_source: str
    loc_saved_est: int
    decl_name: str = ""
    priority: int = 50


@dataclass
class AppliedEdit:
    """Record of a kernel-verified simplification edit accepted by the gate."""

    rule: str
    description: str
    decl_name: str
    before_loc: int
    after_loc: int
    loc_saved: int
    elapsed_s: float


@dataclass
class RejectedEdit:
    """Record of a candidate edit rejected and reverted by the verification gate."""

    rule: str
    description: str
    decl_name: str
    reason: str


@dataclass
class SimplifyResult:
    """End-to-end Stage 4 simplification outcome for one Lean 4 module."""

    module: str
    file_path: str
    changed: bool
    before_loc: int
    after_loc: int
    loc_saved: int
    before_steps: int
    after_steps: int
    steps_saved: int
    exported_decls: list[str] = field(default_factory=list)
    axioms: dict[str, list[str]] = field(default_factory=dict)
    baseline_signatures: dict[str, str] = field(default_factory=dict)
    accepted_edits: list[AppliedEdit] = field(default_factory=list)
    rejected_edits: list[RejectedEdit] = field(default_factory=list)
    build_time_s: float = 0.0
    gate_passed: bool = False
    errors: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def count_proof_steps(source: str) -> int:
    """Count non-comment tactic/proof lines inside theorem/lemma bodies."""
    if not source:
        return 0
    lines = source.splitlines()
    steps = 0
    in_proof = False
    in_theorem_sig = False
    block_depth = 0
    mods = r"(?:(?:private|protected|public|noncomputable|unsafe|partial|local|scoped)\s+)*"
    decl_start_re = re.compile(
        rf"^(?:@\[[^\]]*\]\s*)*{mods}(?:theorem|lemma)\b"
    )
    top_stop_re = re.compile(
        rf"^(?:@\[[^\]]*\]|{mods}(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|"
        r"opaque|constant|namespace|section|end|open|variable|universe|attribute|set_option|"
        r"example|macro|syntax|elab|declare_aesop_rule_sets)\b)"
    )
    for raw in lines:
        s = raw.strip()
        if block_depth > 0:
            block_depth += s.count("/-") - s.count("-/")
            if block_depth < 0:
                block_depth = 0
            continue
        if s.startswith("/-"):
            block_depth += s.count("/-") - s.count("-/")
            if block_depth < 0:
                block_depth = 0
            continue
        if not s or s.startswith("--"):
            continue
        code = s.split("--", 1)[0].strip()
        if not code:
            continue
        if not raw.startswith((" ", "\t")) and top_stop_re.match(code):
            in_proof = False
            in_theorem_sig = False
        if decl_start_re.match(code):
            if ":=" in code:
                in_proof = True
                in_theorem_sig = False
                rhs = code.split(":=", 1)[1].strip()
                if rhs and rhs != "by":
                    steps += max(1, rhs.count(";") + 1)
            else:
                in_proof = False
                in_theorem_sig = True
            continue
        if in_theorem_sig and ":=" in code:
            in_theorem_sig = False
            in_proof = True
            rhs = code.split(":=", 1)[1].strip()
            if rhs and rhs != "by":
                steps += max(1, rhs.count(";") + 1)
            continue
        if in_proof:
            steps += max(1, code.count(";") + 1)
    return steps


def _wrap_runner_with_env(
    env_overrides: dict[str, str] | None,
    command_runner: CommandRunner | None,
) -> CommandRunner | None:
    """Wrap a CommandRunner (or default subprocess runner) with env overrides."""
    if not env_overrides and command_runner is None:
        return None
    if not env_overrides:
        return command_runner

    def _wrapped(
        cmd: list[str], cwd: Path, env: dict[str, str], timeout_s: int
    ) -> tuple[int, str, str]:
        merged = dict(env)
        merged.update(env_overrides)
        if "PATH" in env_overrides and "PATH" in env:
            # Ensure env_overrides PATH takes precedence while keeping system PATH
            merged["PATH"] = f"{env_overrides['PATH']}{os.pathsep}{env['PATH']}"
        if command_runner is not None:
            return command_runner(cmd, cwd, merged, timeout_s)
        return _run_subprocess_clean(cmd, cwd, merged, timeout_s)

    return _wrapped


def _read_source(fpath: Path) -> tuple[str, str | None]:
    """Read `fpath` and return `(text, newline)` so writes keep the original line endings."""
    raw = fpath.read_bytes()
    return raw.decode("utf-8").replace("\r\n", "\n"), ("\r\n" if b"\r\n" in raw else None)


def _write_source(fpath: Path, text: str, newline: str | None) -> None:
    fpath.write_text(text, encoding="utf-8", newline=newline)


def _resolve_module_file(project_dir: Path, module_name: str, file_path: str | Path | None) -> Path:
    if file_path is not None:
        return Path(file_path)
    rel = Path(*module_name.split(".")).with_suffix(".lean")
    cand_src = project_dir / "src" / rel
    if cand_src.exists():
        return cand_src
    cand_root = project_dir / rel
    if cand_root.exists():
        return cand_root
    return cand_src


def extract_exported_decls(source: str, module_name: str) -> list[str]:
    """Return fully-qualified exported non-private declaration names in `source`."""
    parsed = parse_lean_source(source, module_name)
    out: list[str] = []
    seen: set[str] = set()
    for d in parsed.declarations:
        if d.is_private:
            continue
        if d.kind not in _DECL_EXPORT_KINDS:
            continue
        if d.name and d.name not in seen:
            seen.add(d.name)
            out.append(d.name)
    return out


def _build_lean_env_and_lake(
    lake_bin: str | None,
    command_runner: CommandRunner | None,
    env_overrides: dict[str, str] | None,
) -> tuple[CommandRunner, dict[str, str], str | None]:
    """Return `(runner, env, resolved_lake)` for Lean/Lake invocations."""
    runner = _wrap_runner_with_env(env_overrides, command_runner) or _run_subprocess_clean
    env = dict(os.environ)
    if env_overrides:
        env.update(env_overrides)
    elan_bin = str(Path.home() / ".elan" / "bin")
    if elan_bin not in env.get("PATH", ""):
        env["PATH"] = f"{elan_bin}{os.pathsep}{env.get('PATH', '')}"
    resolved_lake = (
        find_lake_binary(lake_bin) if command_runner is None else (lake_bin or "lake")
    )
    return runner, env, resolved_lake


def _inspect_module_decls(
    proj_path: Path,
    module_name: str,
    decls: Sequence[str],
    resolved_lake: str,
    env: dict[str, str],
    timeout_s: int,
    runner: CommandRunner,
) -> tuple[int, dict[str, str], dict[str, list[str]], str]:
    """Run `#check` and `#print axioms` on `decls` inside `module_name`."""
    if not decls:
        return 0, {}, {}, ""
    script_lines = [f"import {module_name}"]
    for decl in decls:
        script_lines.append(f"#check @{decl}")
        script_lines.append(f"#print axioms {decl}")
    script_text = "\n".join(script_lines) + "\n"

    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".lean",
        prefix="pc_decl_",
        delete=False,
        encoding="utf-8",
    ) as tf:
        tf.write(script_text)
        tmp_path = Path(tf.name)

    try:
        arc, aout, aerr = runner(
            [resolved_lake, "env", "lean", str(tmp_path)], proj_path, env, timeout_s
        )
    finally:
        try:
            tmp_path.unlink(missing_ok=True)
        except OSError:
            pass

    combined = f"{aout}\n{aerr}"
    sigs = parse_check_signatures(combined)
    axioms = _parse_print_axioms_safe(combined)
    detail = aerr.strip() or aout.strip()
    return arc, sigs, axioms, detail


def capture_baseline_signatures(
    project_dir: str | Path,
    module_name: str,
    exported_decls: Sequence[str],
    *,
    lake_bin: str | None = None,
    timeout_s: int = 300,
    command_runner: CommandRunner | None = None,
    env_overrides: dict[str, str] | None = None,
) -> tuple[bool, dict[str, str], dict[str, list[str]], float, str]:
    """Compile baseline module and capture exact `#check` types and `#print axioms`."""
    proj_path = Path(project_dir)
    runner, env, resolved_lake = _build_lean_env_and_lake(
        lake_bin, command_runner, env_overrides
    )
    if not resolved_lake:
        return False, {}, {}, 0.0, "Could not locate `lake` binary."

    t0 = time.perf_counter()
    rc, out, err = runner([resolved_lake, "build", module_name], proj_path, env, timeout_s)
    elapsed = round(time.perf_counter() - t0, 3)
    if rc != 0:
        detail = "\n".join(x for x in (out.strip(), err.strip()) if x)
        return False, {}, {}, elapsed, f"Baseline `lake build {module_name}` failed (rc={rc}): {detail}"

    if not exported_decls:
        return True, {}, {}, elapsed, ""

    arc, sigs, axioms, detail = _inspect_module_decls(
        proj_path, module_name, exported_decls, resolved_lake, env, timeout_s, runner
    )
    if arc != 0:
        return (
            False,
            sigs,
            axioms,
            elapsed,
            f"Baseline `#check`/`#print axioms` failed (rc={arc}): {detail}",
        )
    return True, sigs, axioms, elapsed, ""


def _run_gate_with_primed_check(
    proj_path: Path,
    module_name: str,
    exported_decls: Sequence[str],
    baseline_sigs: dict[str, str],
    *,
    before_loc: int,
    after_loc: int,
    lake_bin: str | None,
    timeout_s: int,
    command_runner: CommandRunner | None,
    env_overrides: dict[str, str] | None,
    baseline_axioms: dict[str, list[str]] | None = None,
) -> GateResult:
    """Run `verify_refactor_gate` with exact `#check` signatures and per-decl axiom invariance.

    Primed names (`C2'`) used to need a separate pass; the gate parser now handles them.
    """
    gate_sigs = (
        {k: v for k, v in baseline_sigs.items() if k in exported_decls}
        if baseline_sigs
        else None
    )
    return verify_refactor_gate(
        proj_path,
        target_modules=[module_name],
        exported_decls=list(exported_decls) or None,
        expected_signatures=gate_sigs,
        before_loc=before_loc,
        after_loc=after_loc,
        allowed_axioms=STANDARD_LEAN_AXIOMS,
        baseline_axioms=baseline_axioms or None,
        min_loc_reduction=1,
        run_lake=True,
        lake_bin=lake_bin,
        timeout_s=timeout_s,
        command_runner=_wrap_runner_with_env(env_overrides, command_runner),
    )


def _indent_of(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _collect_indented_block(lines: list[str], start_idx: int) -> int:
    """Return inclusive end line index of a Lean block starting at `start_idx`."""
    base_indent = _indent_of(lines[start_idx])
    end_idx = start_idx
    i = start_idx + 1
    while i < len(lines):
        stripped = lines[i].strip()
        if not stripped:
            i += 1
            continue
        ind = _indent_of(lines[i])
        if ind <= base_indent:
            break
        end_idx = i
        i += 1
    return end_idx


def _find_declaration_proof_spans(
    lines: list[str], decl: ParsedDecl
) -> tuple[int | None, int, int]:
    """Return `(by_line_idx, proof_start_idx, proof_end_idx)` (0-based) for `decl`."""
    s_idx = max(0, decl.start_line - 1)
    e_idx = min(len(lines) - 1, decl.end_line - 1)
    for i in range(s_idx, e_idx + 1):
        stripped = lines[i].strip()
        # Look for `:= by` at end of line (not inside comment)
        code = stripped.split("--", 1)[0].rstrip()
        if re.search(r":=\s*by\s*$", code):
            return i, i + 1, e_idx
    return None, s_idx, e_idx


def _is_ident_used_in_lines(ident: str, lines: Sequence[str]) -> bool:
    pat = re.compile(rf"(?<![A-Za-z0-9_'\.]){re.escape(ident)}(?![A-Za-z0-9_'])")
    for ln in lines:
        code = ln.split("--", 1)[0]
        if pat.search(code):
            return True
    return False


def find_dead_have_candidates(source: str, module_name: str) -> list[SimplifyCandidate]:
    """Detect dead local `have`/`let`/`set` bindings and unused `private` lemmas."""
    candidates: list[SimplifyCandidate] = []
    lines = source.splitlines()
    parsed = parse_lean_source(source, module_name)

    # 1. Dead `private lemma` / `private theorem` (not tagged with @[simp]/@[ext]/etc.)
    for decl in parsed.declarations:
        if not decl.is_private or decl.kind not in ("theorem", "lemma"):
            continue
        s_idx = max(0, decl.start_line - 1)
        e_idx = min(len(lines) - 1, decl.end_line - 1)
        header_window = "\n".join(lines[max(0, s_idx - 2) : s_idx + 1])
        if re.search(r"@\[[^\]]*(?:simp|ext|instance|aesop|norm_cast|measurability|fun_prop)", header_window):
            continue
        other_lines = lines[:s_idx] + lines[e_idx + 1 :]
        if not _is_ident_used_in_lines(decl.short_name, other_lines):
            new_lines = lines[:s_idx] + lines[e_idx + 1 :]
            new_src = "\n".join(new_lines) + ("\n" if source.endswith("\n") else "")
            loc_saved = max(1, count_effective_loc(source) - count_effective_loc(new_src))
            candidates.append(
                SimplifyCandidate(
                    rule="prune_dead_private",
                    description=f"Remove unused private {decl.kind} `{decl.short_name}`",
                    new_source=new_src,
                    loc_saved_est=loc_saved,
                    decl_name=decl.name,
                    priority=90,
                )
            )

    # 2. Dead local `have` / `let` / `set` inside `:= by` proof blocks
    for decl in parsed.declarations:
        if decl.kind not in ("theorem", "lemma", "def"):
            continue
        by_idx, p_start, p_end = _find_declaration_proof_spans(lines, decl)
        if by_idx is None or p_start > p_end:
            continue
        i = p_start
        while i <= p_end:
            line = lines[i]
            m = _HAVE_LINE_RE.match(line)
            if m:
                indent_str, kw, ident, rest = m.groups()
                # Skip `haveI` / `letI` (matched only if space after `have`/`let`, safe),
                # skip `this`, `_`, and instance-style bindings.
                if ident in ("this", "_") or ident.startswith("inst"):
                    i += 1
                    continue
                # Find extent of RHS of this `have`/`let`/`set`
                stmt_end = _collect_indented_block(lines, i)
                stmt_end = min(stmt_end, p_end)
                tail_lines = lines[stmt_end + 1 : p_end + 1]
                # Check if `ident` is referenced in the rest of the declaration
                if not _is_ident_used_in_lines(ident, tail_lines):
                    # Also check `set x := e with hx` where `hx` might be used even if `x` isn't
                    extra_used = False
                    if kw == "set":
                        wm = _SET_WITH_RE.match(line)
                        if wm and _is_ident_used_in_lines(wm.group(2), tail_lines):
                            extra_used = True
                    if not extra_used:
                        new_lines = lines[:i] + lines[stmt_end + 1 :]
                        new_src = "\n".join(new_lines) + ("\n" if source.endswith("\n") else "")
                        saved = count_effective_loc(source) - count_effective_loc(new_src)
                        if saved >= 1:
                            prio = 85 if not _CONTEXT_TACTICS_RE.search("\n".join(tail_lines)) else 35
                            candidates.append(
                                SimplifyCandidate(
                                    rule=f"prune_dead_{kw}",
                                    description=f"Prune unused `{kw} {ident}` in `{decl.short_name}`",
                                    new_source=new_src,
                                    loc_saved_est=saved,
                                    decl_name=decl.name,
                                    priority=prio,
                                )
                            )
            i += 1

    return candidates


def _detect_tactic_probes(block_text: str) -> list[str]:
    """Order Lean 4 automation tactics most likely to close `block_text`."""
    probes: list[str] = []
    if re.search(r"[ℕℤ<≤>≥+\-]|Fin\s|omega|Nat\.|Int\.", block_text):
        probes.extend(["omega", "linarith", "nlinarith", "norm_num", "positivity", "decide"])
    if re.search(r"[ℝℂ/^]|ring|field_simp|mul_|add_|sub_", block_text):
        for tac in ("linarith", "ring", "nlinarith", "positivity", "norm_num", "field_simp; ring"):
            if tac not in probes:
                probes.append(tac)
    for tac in ("simp_all", "aesop", "grind", "rfl", "tauto", "omega", "linarith", "ring", "positivity"):
        if tac not in probes:
            probes.append(tac)
    return probes[:8]


def find_tactic_collapse_candidates(source: str, module_name: str) -> list[SimplifyCandidate]:
    """Generate tactic-collapse and automation-lifting candidates."""
    candidates: list[SimplifyCandidate] = []
    lines = source.splitlines()
    parsed = parse_lean_source(source, module_name)
    newline_end = "\n" if source.endswith("\n") else ""

    # 1. Module-wide structural tactic collapses (line-pair / block patterns)
    n = len(lines)
    i = 0
    while i < n:
        ln = lines[i]

        # Pattern B1a: `have := <expr>` followed by `exact this` or `simpa [...] using this`
        m_anon = _ANON_HAVE_RE.match(ln)
        if m_anon and i + 1 < n:
            ind, rhs = m_anon.group(1), m_anon.group(2).strip()
            if not rhs.startswith("by"):
                nxt = lines[i + 1]
                m_ex = _EXACT_IDENT_RE.match(nxt)
                if m_ex and m_ex.group(2) == "this":
                    new_lines = lines[:i] + [f"{m_ex.group(1)}exact {rhs}"] + lines[i + 2 :]
                    candidates.append(
                        SimplifyCandidate(
                            rule="collapse_have_this",
                            description=f"Collapse `have := ...; exact this` at line {i + 1}",
                            new_source="\n".join(new_lines) + newline_end,
                            loc_saved_est=1,
                            priority=80,
                        )
                    )
                m_smp = _SIMPA_USING_IDENT_RE.match(nxt)
                if m_smp and m_smp.group(3) == "this":
                    new_lines = lines[:i] + [f"{m_smp.group(1)}{m_smp.group(2)} {rhs}"] + lines[i + 2 :]
                    candidates.append(
                        SimplifyCandidate(
                            rule="collapse_have_simpa",
                            description=f"Collapse `have := ...; simpa using this` at line {i + 1}",
                            new_source="\n".join(new_lines) + newline_end,
                            loc_saved_est=1,
                            priority=80,
                        )
                    )

        # Pattern B1b: single-line `have h := <expr>` followed by `exact h` or `simpa ... using h`
        m_have = _HAVE_LINE_RE.match(ln)
        if m_have and m_have.group(2) == "have" and i + 1 < n and ":=" in m_have.group(4):
            hname = m_have.group(3)
            rhs = m_have.group(4).split(":=", 1)[1].strip()
            if rhs and not rhs.startswith("by") and ":" not in m_have.group(4).split(":=", 1)[0]:
                nxt = lines[i + 1]
                m_ex = _EXACT_IDENT_RE.match(nxt)
                if m_ex and m_ex.group(2) == hname:
                    new_lines = lines[:i] + [f"{m_ex.group(1)}exact {rhs}"] + lines[i + 2 :]
                    candidates.append(
                        SimplifyCandidate(
                            rule="collapse_have_exact",
                            description=f"Collapse `have {hname} := ...; exact {hname}` at line {i + 1}",
                            new_source="\n".join(new_lines) + newline_end,
                            loc_saved_est=1,
                            priority=80,
                        )
                    )
                m_smp = _SIMPA_USING_IDENT_RE.match(nxt)
                if m_smp and m_smp.group(3) == hname:
                    new_lines = lines[:i] + [f"{m_smp.group(1)}{m_smp.group(2)} {rhs}"] + lines[i + 2 :]
                    candidates.append(
                        SimplifyCandidate(
                            rule="collapse_have_simpa",
                            description=f"Collapse `have {hname} := ...; simpa using {hname}` at line {i + 1}",
                            new_source="\n".join(new_lines) + newline_end,
                            loc_saved_est=1,
                            priority=80,
                        )
                    )

        # Pattern B2: `first\n  | branch1\n  | branch2` compatibility scaffolding
        m_first = _FIRST_HEADER_RE.match(ln)
        if m_first:
            ind = m_first.group(1)
            base_len = len(ind)
            j = i + 1
            branches: list[tuple[int, list[str]]] = []
            pipe_len: int | None = None
            while j < n:
                mb = _FIRST_BRANCH_RE.match(lines[j])
                if mb and len(mb.group(1)) >= base_len and (
                    pipe_len is None or len(mb.group(1)) == pipe_len
                ):
                    pipe_len = len(mb.group(1))
                    branch_text = mb.group(2).strip()
                    branch_col = lines[j].find(mb.group(2))
                    if branch_col < 0:
                        branch_col = pipe_len + 2
                    branches.append((branch_col, [branch_text]))
                    j += 1
                elif (
                    branches
                    and pipe_len is not None
                    and lines[j].strip()
                    and _indent_of(lines[j]) > pipe_len
                ):
                    branches[-1][1].append(lines[j])
                    j += 1
                else:
                    break
            if len(branches) >= 2 and pipe_len is not None:
                for b_idx, (branch_col, br_lines) in enumerate(branches):
                    first_line = br_lines[0]
                    work_lines = list(br_lines)
                    expr_col = branch_col
                    if len(work_lines) == 1 and first_line.startswith("(") and first_line.endswith(")"):
                        first_line = first_line[1:-1].strip()
                    elif (
                        len(work_lines) >= 2
                        and first_line.startswith("(")
                        and work_lines[-1].rstrip().endswith(")")
                    ):
                        after_paren = first_line[1:]
                        expr_col = branch_col + 1 + (len(after_paren) - len(after_paren.lstrip()))
                        first_line = after_paren.lstrip()
                        work_lines[-1] = work_lines[-1].rstrip()[:-1]
                    rep_lines = [f"{ind}{first_line}"]
                    for cont_ln in work_lines[1:]:
                        shift = max(0, _indent_of(cont_ln) - expr_col)
                        rep_lines.append(f"{ind}{' ' * shift}{cont_ln.lstrip()}")
                    new_lines = lines[:i] + rep_lines + lines[j:]
                    new_src = "\n".join(new_lines) + newline_end
                    saved = max(1, count_effective_loc(source) - count_effective_loc(new_src))
                    candidates.append(
                        SimplifyCandidate(
                            rule="collapse_first_branch",
                            description=f"Replace `first` combinator at line {i + 1} with branch {b_idx + 1}",
                            new_source=new_src,
                            loc_saved_est=saved,
                            priority=83 if b_idx == 0 else 80,
                        )
                    )
                i = j
                continue

        # Pattern B3: `:= by\n  exact <expr>` -> `:= <expr>` (or `rfl`)
        if re.search(r":=\s*by\s*$", ln) and i + 1 < n:
            nxt_s = lines[i + 1].strip()
            m_ex_rhs = re.match(r"^(?:exact\s+(.+)|rfl)$", nxt_s)
            if m_ex_rhs:
                # Only collapse if the next non-blank line after i+1 is not deeper-indented part of same tactic
                end_tac = _collect_indented_block(lines, i + 1)
                if end_tac == i + 1 and (
                    i + 2 >= n or not lines[i + 2].strip() or _indent_of(lines[i + 2]) <= _indent_of(ln)
                ):
                    term_rhs = m_ex_rhs.group(1) if m_ex_rhs.group(1) else "rfl"
                    replaced_hdr = re.sub(r":=\s*by\s*$", f":= {term_rhs}", ln)
                    new_lines = lines[:i] + [replaced_hdr] + lines[i + 2 :]
                    candidates.append(
                        SimplifyCandidate(
                            rule="collapse_by_exact",
                            description=f"Collapse `:= by exact/rfl` to term mode at line {i + 1}",
                            new_source="\n".join(new_lines) + newline_end,
                            loc_saved_est=1,
                            priority=78,
                        )
                    )

        # Pattern B3b: bare bullet `·` followed by single-line tactic -> `· <tac>`
        if ln.strip() == "·" and i + 1 < n:
            nxt_s = lines[i + 1].strip()
            if (
                nxt_s
                and not nxt_s.startswith(("--", "/-", "|", "·"))
                and _indent_of(lines[i + 1]) > _indent_of(ln)
            ):
                # Only collapse if the line after i+1 does NOT continue a multi-line sub-block
                if i + 2 >= n or not lines[i + 2].strip() or _indent_of(lines[i + 2]) <= _indent_of(ln):
                    ind = " " * _indent_of(ln)
                    new_lines = lines[:i] + [f"{ind}· {nxt_s}"] + lines[i + 2 :]
                    candidates.append(
                        SimplifyCandidate(
                            rule="collapse_bare_bullet",
                            description=f"Merge bare bullet `·` with single tactic at line {i + 1}",
                            new_source="\n".join(new_lines) + newline_end,
                            loc_saved_est=1,
                            priority=77,
                        )
                    )

        # Pattern B4: consecutive `rw [a]` / `rw [b]` at exact same indentation
        m_rw1 = _RW_SINGLE_RE.match(ln)
        if m_rw1 and i + 1 < n:
            m_rw2 = _RW_SINGLE_RE.match(lines[i + 1])
            if m_rw2 and m_rw1.group(1) == m_rw2.group(1):
                merged = f"{m_rw1.group(1)}rw [{m_rw1.group(2)}, {m_rw2.group(2)}]"
                new_lines = lines[:i] + [merged] + lines[i + 2 :]
                candidates.append(
                    SimplifyCandidate(
                        rule="merge_rw_chain",
                        description=f"Merge consecutive `rw` steps at lines {i + 1}-{i + 2}",
                        new_source="\n".join(new_lines) + newline_end,
                        loc_saved_est=1,
                        priority=70,
                    )
                )

        i += 1

    # 2. Declaration-level subproof & whole-proof automation lifting
    for decl in parsed.declarations:
        if decl.kind not in ("theorem", "lemma"):
            continue
        by_idx, p_start, p_end = _find_declaration_proof_spans(lines, decl)
        if by_idx is None or p_start > p_end:
            continue
        proof_lines = lines[p_start : p_end + 1]
        proof_eff_loc = sum(1 for x in proof_lines if x.strip() and not x.strip().startswith("--"))

        # Lift multi-line `calc` blocks inside the proof
        k = p_start
        while k <= p_end:
            ks = lines[k].lstrip()
            if ks.startswith("calc ") or ks == "calc":
                calc_end = min(_collect_indented_block(lines, k), p_end)
                calc_loc = sum(
                    1 for x in lines[k : calc_end + 1] if x.strip() and not x.strip().startswith("--")
                )
                if calc_loc >= 3:
                    ind_str = " " * _indent_of(lines[k])
                    calc_text = "\n".join(lines[k : calc_end + 1])
                    for tac in _detect_tactic_probes(calc_text):
                        if tac in ("decide", "rfl"):
                            continue
                        new_lines = lines[:k] + [f"{ind_str}{tac}"] + lines[calc_end + 1 :]
                        candidates.append(
                            SimplifyCandidate(
                                rule="lift_calc_chain",
                                description=f"Collapse `calc` block ({calc_loc} LOC) in `{decl.short_name}` to `{tac}`",
                                new_source="\n".join(new_lines) + newline_end,
                                loc_saved_est=calc_loc - 1,
                                decl_name=decl.name,
                                priority=65,
                            )
                        )
                k = calc_end + 1
                continue

            # Lift multi-line `have h ... := by ...` subproofs
            mh = _HAVE_LINE_RE.match(lines[k])
            if mh and re.search(r":=\s*by\s*$", lines[k]):
                sub_end = min(_collect_indented_block(lines, k), p_end)
                sub_loc = sum(
                    1 for x in lines[k + 1 : sub_end + 1] if x.strip() and not x.strip().startswith("--")
                )
                if sub_loc >= 2:
                    sub_text = "\n".join(lines[k : sub_end + 1])
                    for tac in _detect_tactic_probes(sub_text)[:5]:
                        hdr = lines[k].rstrip()
                        new_lines = lines[:k] + [f"{hdr} {tac}"] + lines[sub_end + 1 :]
                        candidates.append(
                            SimplifyCandidate(
                                rule="lift_subproof_automation",
                                description=f"Collapse `have {mh.group(3)}` subproof ({sub_loc} lines) in `{decl.short_name}` to `by {tac}`",
                                new_source="\n".join(new_lines) + newline_end,
                                loc_saved_est=sub_loc,
                                decl_name=decl.name,
                                priority=60,
                            )
                        )
            k += 1

        # Lift compact whole-theorem proofs (2..18 lines) to single-tactic automation
        if 2 <= proof_eff_loc <= 18:
            body_text = "\n".join(proof_lines)
            for tac in _detect_tactic_probes(body_text)[:5]:
                hdr = re.sub(r":=\s*by\s*$", f":= by {tac}", lines[by_idx])
                new_lines = lines[:by_idx] + [hdr] + lines[p_end + 1 :]
                candidates.append(
                    SimplifyCandidate(
                        rule="lift_proof_automation",
                        description=f"Collapse `{decl.short_name}` proof ({proof_eff_loc} LOC) to `by {tac}`",
                        new_source="\n".join(new_lines) + newline_end,
                        loc_saved_est=proof_eff_loc,
                        decl_name=decl.name,
                        priority=75,
                    )
                )

    return candidates


def _lookup_mathlib_match_in_db(db_path: Path, c_hash: str) -> str | None:
    if not c_hash or not db_path.exists():
        return None
    try:
        conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
        try:
            row = conn.execute(
                """
                SELECT name FROM declarations
                WHERE is_mathlib = 1 AND canonical_type_hash = ?
                LIMIT 1
                """,
                (c_hash,),
            ).fetchone()
            return str(row[0]) if row else None
        finally:
            conn.close()
    except sqlite3.Error:
        return None


def find_mathlib_absorption_candidates(
    source: str,
    module_name: str,
    *,
    db_path: str | Path | None = None,
) -> list[SimplifyCandidate]:
    """Identify bespoke helper lemmas duplicating Mathlib theorems or inlineable wrappers."""
    candidates: list[SimplifyCandidate] = []
    lines = source.splitlines()
    parsed = parse_lean_source(source, module_name)
    newline_end = "\n" if source.endswith("\n") else ""
    db_p = Path(db_path) if db_path else None

    for decl in parsed.declarations:
        if decl.kind not in ("theorem", "lemma"):
            continue
        s_idx = max(0, decl.start_line - 1)
        e_idx = min(len(lines) - 1, decl.end_line - 1)
        canon_sig = canonicalize_type(decl.type_sig)

        # 1. Exact canonical_type_hash match against Mathlib DB
        mathlib_name: str | None = None
        note = ""
        if db_p is not None:
            c_hash = decl.canonical_type_hash or canonical_type_hash(decl.type_sig)
            mathlib_name = _lookup_mathlib_match_in_db(db_p, c_hash)
            if mathlib_name:
                note = "DB canonical_type_hash match"

        # 2. Structural Mathlib signature patterns
        if mathlib_name is None:
            for pat, mname, mnote in _MATHLIB_CANONICAL_PATTERNS:
                if pat.search(canon_sig):
                    mathlib_name = mname
                    note = mnote
                    break

        if mathlib_name is not None and decl.body_loc >= 2:
            # Candidate A: delegate helper body directly to `exact <mathlib_name> ...` / `by exact_mod_cast ...`
            by_idx, p_start, p_end = _find_declaration_proof_spans(lines, decl)
            if by_idx is not None and p_end > by_idx:
                for wrapper in (
                    f":= {mathlib_name}",
                    f":= by simpa using {mathlib_name}",
                    f":= by exact {mathlib_name} _",
                ):
                    hdr = re.sub(r":=\s*by\s*$", wrapper, lines[by_idx])
                    new_lines = lines[:by_idx] + [hdr] + lines[p_end + 1 :]
                    saved = count_effective_loc(source) - count_effective_loc("\n".join(new_lines))
                    if saved >= 1:
                        candidates.append(
                            SimplifyCandidate(
                                rule="absorb_mathlib_helper",
                                description=f"Delegate `{decl.short_name}` to Mathlib `{mathlib_name}` ({note})",
                                new_source="\n".join(new_lines) + newline_end,
                                loc_saved_est=saved,
                                decl_name=decl.name,
                                priority=72,
                            )
                        )

            # Candidate B: for private helpers, also try substituting call sites with Mathlib theorem directly
            if decl.is_private:
                other_lines = lines[:s_idx] + lines[e_idx + 1 :]
                pat_call = re.compile(
                    rf"(?<![A-Za-z0-9_'\.]){re.escape(decl.short_name)}(?![A-Za-z0-9_'])"
                )
                if any(pat_call.search(ol.split("--", 1)[0]) for ol in other_lines):
                    new_other = [pat_call.sub(mathlib_name, ol) for ol in other_lines]
                    new_src = "\n".join(new_other) + newline_end
                    saved = count_effective_loc(source) - count_effective_loc(new_src)
                    if saved >= 1:
                        candidates.append(
                            SimplifyCandidate(
                                rule="absorb_mathlib_inline",
                                description=f"Replace private `{decl.short_name}` with direct Mathlib `{mathlib_name}` calls",
                                new_source=new_src,
                                loc_saved_est=saved,
                                decl_name=decl.name,
                                priority=76,
                            )
                        )

    return candidates


def _build_batch_candidate(
    source: str,
    module_name: str,
    *,
    db_path: str | Path | None = None,
) -> SimplifyCandidate | None:
    """Greedily chain safe deterministic line/dead-binding rewrites into one batch candidate."""
    high_conf_rules = frozenset(
        {
            "prune_dead_private",
            "prune_dead_have",
            "prune_dead_let",
            "prune_dead_set",
            "collapse_have_this",
            "collapse_have_simpa",
            "collapse_have_exact",
            "collapse_by_exact",
            "collapse_bare_bullet",
            "merge_rw_chain",
        }
    )
    curr = source
    applied_rules: list[str] = []
    for _ in range(24):
        step_cands: list[SimplifyCandidate] = []
        step_cands.extend(find_dead_have_candidates(curr, module_name))
        step_cands.extend(find_tactic_collapse_candidates(curr, module_name))
        if db_path is not None:
            step_cands.extend(
                find_mathlib_absorption_candidates(curr, module_name, db_path=db_path)
            )
        picked = next(
            (
                c
                for c in step_cands
                if (c.rule in high_conf_rules and c.priority >= 70)
                or c.rule in ("absorb_mathlib_inline", "absorb_mathlib_helper")
            ),
            None,
        )
        if picked is None or picked.new_source == curr:
            break
        curr = picked.new_source
        applied_rules.append(picked.rule)
    saved = count_effective_loc(source) - count_effective_loc(curr)
    if len(applied_rules) >= 2 and saved >= 2:
        summary = ", ".join(sorted(set(applied_rules)))
        return SimplifyCandidate(
            rule="batch_high_confidence",
            description=f"Batch {len(applied_rules)} high-confidence rewrites ({summary})",
            new_source=curr,
            loc_saved_est=saved,
            priority=95,
        )
    return None


def generate_simplify_candidates(
    source: str,
    module_name: str,
    *,
    db_path: str | Path | None = None,
) -> list[SimplifyCandidate]:
    """Collect and deduplicate all candidate simplifications sorted by priority & LOC gain."""
    raw: list[SimplifyCandidate] = []
    batch = _build_batch_candidate(source, module_name, db_path=db_path)
    if batch is not None:
        raw.append(batch)
    raw.extend(find_dead_have_candidates(source, module_name))
    raw.extend(find_tactic_collapse_candidates(source, module_name))
    raw.extend(find_mathlib_absorption_candidates(source, module_name, db_path=db_path))

    seen_src: set[str] = {source}
    unique: list[SimplifyCandidate] = []
    for cand in raw:
        if cand.new_source in seen_src:
            continue
        if count_effective_loc(cand.new_source) >= count_effective_loc(source):
            continue
        seen_src.add(cand.new_source)
        unique.append(cand)

    unique.sort(key=lambda c: (-c.priority, -c.loc_saved_est, c.rule))
    return unique


def simplify_module(
    project_dir: str | Path,
    module_name: str,
    *,
    file_path: str | Path | None = None,
    db_path: str | Path | None = None,
    lake_bin: str | None = None,
    timeout_s: int = 300,
    max_candidates: int = 30,
    max_rounds: int = 6,
    command_runner: CommandRunner | None = None,
    env_overrides: dict[str, str] | None = None,
    dry_run: bool = False,
) -> SimplifyResult:
    """Iteratively simplify `module_name` with strict Stage 4 kernel-gate verification.

    Every candidate rewrite is verified via :func:`verify_refactor_gate`
    (``lake build`` + verbatim ``#check`` exported-type equivalence +
    ``#print axioms`` subset of ``STANDARD_LEAN_AXIOMS`` + strict effective LOC
    reduction). Any failed rewrite is automatically reverted.
    """
    proj_path = Path(project_dir)
    fpath = _resolve_module_file(proj_path, module_name, file_path)
    if not fpath.is_file():
        return SimplifyResult(
            module=module_name,
            file_path=str(fpath),
            changed=False,
            before_loc=0,
            after_loc=0,
            loc_saved=0,
            before_steps=0,
            after_steps=0,
            steps_saved=0,
            gate_passed=False,
            errors=[f"Module source file not found: {fpath}"],
        )

    original_source, newline = _read_source(fpath)
    before_loc = count_effective_loc(original_source)
    before_steps = count_proof_steps(original_source)
    exported_decls = extract_exported_decls(original_source, module_name)

    baseline_sigs: dict[str, str] = {}
    baseline_axioms: dict[str, list[str]] = {}
    baseline_time = 0.0
    if not dry_run:
        ok, baseline_sigs, baseline_axioms, baseline_time, b_err = capture_baseline_signatures(
            proj_path,
            module_name,
            exported_decls,
            lake_bin=lake_bin,
            timeout_s=timeout_s,
            command_runner=command_runner,
            env_overrides=env_overrides,
        )
        if not ok:
            return SimplifyResult(
                module=module_name,
                file_path=str(fpath),
                changed=False,
                before_loc=before_loc,
                after_loc=before_loc,
                loc_saved=0,
                before_steps=before_steps,
                after_steps=before_steps,
                steps_saved=0,
                exported_decls=exported_decls,
                axioms=baseline_axioms,
                baseline_signatures=baseline_sigs,
                build_time_s=baseline_time,
                gate_passed=False,
                errors=[b_err],
            )

    current_source = original_source
    current_loc = before_loc
    accepted: list[AppliedEdit] = []
    rejected: list[RejectedEdit] = []
    tried_hashes: set[str] = set()
    probes_used = 0
    latest_axioms = baseline_axioms

    for _round in range(max_rounds):
        if probes_used >= max_candidates:
            break
        candidates = generate_simplify_candidates(
            current_source, module_name, db_path=db_path
        )
        round_accepted = False
        for cand in candidates:
            if probes_used >= max_candidates:
                break
            ch = hashlib.sha1(cand.new_source.encode("utf-8")).hexdigest()
            if ch in tried_hashes:
                continue
            tried_hashes.add(ch)
            probes_used += 1

            cand_loc = count_effective_loc(cand.new_source)
            if dry_run:
                accepted.append(
                    AppliedEdit(
                        rule=cand.rule,
                        description=cand.description,
                        decl_name=cand.decl_name,
                        before_loc=current_loc,
                        after_loc=cand_loc,
                        loc_saved=current_loc - cand_loc,
                        elapsed_s=0.0,
                    )
                )
                current_source = cand.new_source
                current_loc = cand_loc
                round_accepted = True
                break

            # Transactional write + kernel gate check + automatic revert on failure.
            # The revert sits in `finally` so Ctrl-C or a runner exception mid-build
            # never leaves an unverified rewrite on disk.
            t_edit = time.perf_counter()
            _write_source(fpath, cand.new_source, newline)
            gate_ok = False
            try:
                gate = _run_gate_with_primed_check(
                    proj_path,
                    module_name,
                    exported_decls,
                    baseline_sigs,
                    before_loc=current_loc,
                    after_loc=cand_loc,
                    lake_bin=lake_bin,
                    timeout_s=timeout_s,
                    command_runner=command_runner,
                    env_overrides=env_overrides,
                    baseline_axioms=baseline_axioms,
                )
                gate_ok = gate.passed
            finally:
                if not gate_ok:
                    _write_source(fpath, current_source, newline)
            dt = round(time.perf_counter() - t_edit, 3)

            if gate.passed:
                accepted.append(
                    AppliedEdit(
                        rule=cand.rule,
                        description=cand.description,
                        decl_name=cand.decl_name,
                        before_loc=current_loc,
                        after_loc=cand_loc,
                        loc_saved=current_loc - cand_loc,
                        elapsed_s=dt,
                    )
                )
                current_source = cand.new_source
                current_loc = cand_loc
                if gate.axiom_check.get("axioms"):
                    latest_axioms = gate.axiom_check["axioms"]
                round_accepted = True
                break
            else:
                rejected.append(
                    RejectedEdit(
                        rule=cand.rule,
                        description=cand.description,
                        decl_name=cand.decl_name,
                        reason="; ".join(gate.errors)[:300] or "Gate check failed",
                    )
                )

        if not round_accepted:
            break

    # Guarantee file on disk matches final accepted source (and re-run final clean check if changed)
    if not dry_run and _read_source(fpath)[0] != current_source:
        _write_source(fpath, current_source, newline)

    after_steps = count_proof_steps(current_source)
    return SimplifyResult(
        module=module_name,
        file_path=str(fpath),
        changed=(current_source != original_source),
        before_loc=before_loc,
        after_loc=current_loc,
        loc_saved=before_loc - current_loc,
        before_steps=before_steps,
        after_steps=after_steps,
        steps_saved=before_steps - after_steps,
        exported_decls=exported_decls,
        axioms=latest_axioms,
        baseline_signatures=baseline_sigs,
        accepted_edits=accepted,
        rejected_edits=rejected,
        build_time_s=baseline_time,
        # Non-dry runs only get here after the baseline built and every kept edit passed
        # the gate. A dry run never ran the gate.
        gate_passed=not dry_run,
    )


def verify_manual_rewrite(
    project_dir: str | Path,
    module_name: str,
    new_source: str,
    *,
    file_path: str | Path | None = None,
    lake_bin: str | None = None,
    timeout_s: int = 300,
    command_runner: CommandRunner | None = None,
    env_overrides: dict[str, str] | None = None,
) -> tuple[bool, GateResult, dict[str, str], dict[str, list[str]], float]:
    """Kernel-verify an explicit rewritten module source against its pre-edit baseline.

    Captures baseline `#check` signatures and `#print axioms` first, writes `new_source`,
    runs :func:`verify_refactor_gate`, and automatically reverts if the gate fails.
    """
    proj_path = Path(project_dir)
    fpath = _resolve_module_file(proj_path, module_name, file_path)
    original_source, newline = _read_source(fpath)
    before_loc = count_effective_loc(original_source)
    after_loc = count_effective_loc(new_source)
    exported_decls = extract_exported_decls(original_source, module_name)

    ok, base_sigs, base_axioms, base_t, b_err = capture_baseline_signatures(
        proj_path,
        module_name,
        exported_decls,
        lake_bin=lake_bin,
        timeout_s=timeout_s,
        command_runner=command_runner,
        env_overrides=env_overrides,
    )
    if not ok:
        fail_gate = GateResult(passed=False, errors=[b_err])
        return False, fail_gate, base_sigs, base_axioms, base_t

    t0 = time.perf_counter()
    _write_source(fpath, new_source, newline)
    gate_ok = False
    try:
        gate = _run_gate_with_primed_check(
            proj_path,
            module_name,
            exported_decls,
            base_sigs,
            before_loc=before_loc,
            after_loc=after_loc,
            lake_bin=lake_bin,
            timeout_s=timeout_s,
            command_runner=command_runner,
            env_overrides=env_overrides,
            baseline_axioms=base_axioms,
        )
        gate_ok = gate.passed
    finally:
        if not gate_ok:
            _write_source(fpath, original_source, newline)
    dt = round(time.perf_counter() - t0, 3)
    return gate.passed, gate, base_sigs, gate.axiom_check.get("axioms", base_axioms), dt


def simplify_modules(
    project_dir: str | Path,
    modules: Sequence[str],
    *,
    db_path: str | Path | None = None,
    lake_bin: str | None = None,
    timeout_s: int = 300,
    max_candidates: int = 30,
    max_rounds: int = 6,
    command_runner: CommandRunner | None = None,
    env_overrides: dict[str, str] | None = None,
    dry_run: bool = False,
) -> list[SimplifyResult]:
    """Run kernel-gated :func:`simplify_module` sequentially across a list of modules."""
    results: list[SimplifyResult] = []
    for mod in modules:
        res = simplify_module(
            project_dir,
            mod,
            db_path=db_path,
            lake_bin=lake_bin,
            timeout_s=timeout_s,
            max_candidates=max_candidates,
            max_rounds=max_rounds,
            command_runner=command_runner,
            env_overrides=env_overrides,
            dry_run=dry_run,
        )
        results.append(res)
    return results

