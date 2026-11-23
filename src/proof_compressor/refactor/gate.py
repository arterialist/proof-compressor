"""Stage 4 kernel-checked refactoring verification gate (`lake build` + `#print axioms` + LOC)."""

from __future__ import annotations

import os
import re
import shutil
import signal
import subprocess
import tempfile
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Callable, Sequence

STANDARD_LEAN_AXIOMS: frozenset[str] = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)

# Command runner signature for testability: (cmd, cwd, env, timeout_s) -> (returncode, stdout, stderr)
CommandRunner = Callable[[list[str], Path, dict[str, str], int], tuple[int, str, str]]


@dataclass
class GateResult:
    """Outcome of running the Stage 4 refactoring verification gate."""

    passed: bool
    loc_check: dict[str, Any] = field(default_factory=dict)
    build_check: dict[str, Any] = field(default_factory=dict)
    axiom_check: dict[str, Any] = field(default_factory=dict)
    signature_check: dict[str, Any] = field(default_factory=dict)
    errors: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def count_effective_loc(source: str) -> int:
    """Count non-blank, non-comment lines of Lean 4 source code."""
    if not source:
        return 0
    effective = 0
    block_depth = 0
    for raw_line in source.splitlines():
        i = 0
        n = len(raw_line)
        has_code = False
        while i < n:
            two = raw_line[i : i + 2]
            if block_depth > 0:
                if two == "/-":
                    block_depth += 1
                    i += 2
                elif two == "-/":
                    block_depth -= 1
                    i += 2
                else:
                    i += 1
            else:
                if two == "/-":
                    block_depth += 1
                    i += 2
                elif two == "--":
                    break
                else:
                    if not raw_line[i].isspace():
                        has_code = True
                    i += 1
        if has_code:
            effective += 1
    return effective


def count_files_effective_loc(paths: Sequence[str | Path]) -> int:
    """Sum effective Lean LOC across a collection of file paths."""
    total = 0
    for p in paths:
        fp = Path(p)
        if fp.is_file():
            total += count_effective_loc(fp.read_text(encoding="utf-8", errors="replace"))
    return total


def parse_print_axioms(output: str) -> dict[str, list[str]]:
    """Parse Lean 4 `#print axioms` output into `{decl_name: [axiom1, ...]}`."""
    result: dict[str, list[str]] = {}
    if not output:
        return result

    # Non-greedy, line-bounded name match so primes anywhere in a name (`C2'`,
    # `mul_le'_of_pos`) survive; `[^']+` would split such names at the first prime.
    pat_deps = re.compile(r"'([^\n]+?)'\s+depends on axioms:\s*\[([^\]]*)\]")
    pat_none = re.compile(r"'([^\n]+?)'\s+does not depend on any axioms")

    for m in pat_deps.finditer(output):
        name = m.group(1).strip()
        raw_axs = m.group(2).strip()
        axs = [a.strip() for a in raw_axs.split(",") if a.strip()]
        result[name] = axs

    for m in pat_none.finditer(output):
        name = m.group(1).strip()
        result.setdefault(name, [])

    return result


def parse_check_signatures(output: str) -> dict[str, str]:
    """Parse Lean 4 `#check @Name` output lines into `{decl_name: normalized_type}`."""
    sigs: dict[str, str] = {}
    if not output:
        return sigs
    # Lean prints `@Foo.bar : <type>` or `Foo.bar : <type>` and wraps long types onto
    # indented continuation lines. Names may contain Unicode (`h₁_pos`) and primes.
    header_re = re.compile(r"^@?([^\s:@'][^\s:]*)\s+:\s*(.*)$")
    name: str | None = None
    parts: list[str] = []

    def _flush() -> None:
        if name is not None:
            sigs[name] = " ".join(" ".join(parts).split())

    for line in output.splitlines():
        if name is not None and line[:1] in (" ", "\t") and line.strip():
            parts.append(line)
            continue
        _flush()
        name, parts = None, []
        m = header_re.match(line)
        if m:
            name, parts = m.group(1), [m.group(2)]
    _flush()
    return sigs


def find_lake_binary(lake_bin: str | None = None) -> str | None:
    """Locate the `lake` binary (explicit path, PATH, or `~/.elan/bin/lake`)."""
    if lake_bin:
        p = Path(lake_bin).expanduser()
        if p.exists():
            return str(p)
        found = shutil.which(lake_bin)
        if found:
            return found
    found = shutil.which("lake")
    if found:
        return found
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.exists():
        return str(elan_lake)
    return None


def _kill_process_group(proc: subprocess.Popen[str]) -> None:
    try:
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    except OSError:
        proc.kill()


def run_subprocess_clean(
    cmd: list[str], cwd: Path, env: dict[str, str], timeout_s: int
) -> tuple[int, str, str]:
    """Run `cmd` in its own process group and kill the whole tree on timeout or interrupt.

    `lake build` spawns `lean` workers; killing only `lake` would leave them compiling a
    candidate that has already been reverted.
    """
    try:
        proc = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
    except OSError as exc:
        return 127, "", str(exc)

    try:
        out, err = proc.communicate(timeout=timeout_s)
        return proc.returncode, out, err
    except subprocess.TimeoutExpired:
        _kill_process_group(proc)
        out, _err = proc.communicate()
        return 124, out or "", f"Command timed out after {timeout_s}s"
    except BaseException:
        # Ctrl-C reaches only our process group (the child runs in its own session).
        _kill_process_group(proc)
        proc.communicate()
        raise


def verify_refactor_gate(
    project_dir: str | Path,
    *,
    target_modules: Sequence[str] | None = None,
    exported_decls: Sequence[str] | None = None,
    expected_signatures: dict[str, str] | None = None,
    before_loc: int | None = None,
    after_loc: int | None = None,
    before_files: Sequence[str | Path] | None = None,
    after_files: Sequence[str | Path] | None = None,
    allowed_axioms: set[str] | frozenset[str] | None = None,
    baseline_axioms: dict[str, list[str]] | None = None,
    check_loc: bool = True,
    min_loc_reduction: int = 1,
    run_lake: bool = True,
    lake_bin: str | None = None,
    timeout_s: int = 300,
    command_runner: CommandRunner | None = None,
) -> GateResult:
    """Run the full Stage 4 verification gate: LOC reduction + `lake build` + `#print axioms`.

    With `baseline_axioms`, each declaration found there must keep its axiom set or shrink
    it (invariance); declarations missing from the baseline are checked against
    `allowed_axioms`. `check_loc=False` skips the LOC test for build-only verification.
    """
    proj_path = Path(project_dir)
    allowed = set(STANDARD_LEAN_AXIOMS if allowed_axioms is None else allowed_axioms)
    runner = command_runner or run_subprocess_clean
    errors: list[str] = []

    # 1. Strict LOC reduction check
    b_loc = before_loc if before_loc is not None else (
        count_files_effective_loc(before_files) if before_files is not None else None
    )
    a_loc = after_loc if after_loc is not None else (
        count_files_effective_loc(after_files) if after_files is not None else None
    )

    loc_passed = True
    if not check_loc:
        loc_check: dict[str, Any] = {"passed": True, "skipped": True}
    elif b_loc is None or a_loc is None:
        loc_passed = False
        errors.append("LOC check requires before_loc/after_loc or before_files/after_files.")
        loc_check = {
            "passed": False,
            "before_loc": b_loc,
            "after_loc": a_loc,
            "reduction": None,
            "min_loc_reduction": min_loc_reduction,
        }
    else:
        reduction = b_loc - a_loc
        pct = round((reduction / b_loc) * 100.0, 2) if b_loc > 0 else 0.0
        loc_passed = reduction >= min_loc_reduction
        if not loc_passed:
            errors.append(
                f"LOC reduction check failed: before={b_loc}, after={a_loc}, "
                f"reduction={reduction} < required {min_loc_reduction}."
            )
        loc_check = {
            "passed": loc_passed,
            "before_loc": b_loc,
            "after_loc": a_loc,
            "reduction": reduction,
            "reduction_pct": pct,
            "min_loc_reduction": min_loc_reduction,
        }

    # Prepare environment with ~/.elan/bin on PATH
    env = dict(os.environ)
    elan_bin = str(Path.home() / ".elan" / "bin")
    if elan_bin not in env.get("PATH", ""):
        env["PATH"] = f"{elan_bin}{os.pathsep}{env.get('PATH', '')}"

    build_check: dict[str, Any] = {"passed": True, "skipped": not run_lake}
    axiom_check: dict[str, Any] = {"passed": True, "skipped": not run_lake or not exported_decls}
    sig_check: dict[str, Any] = {"passed": True, "skipped": not expected_signatures or not run_lake}

    if run_lake:
        resolved_lake = find_lake_binary(lake_bin) if command_runner is None else (lake_bin or "lake")
        if not resolved_lake:
            msg = "Could not locate `lake` binary in PATH or ~/.elan/bin/lake."
            errors.append(msg)
            build_check = {"passed": False, "skipped": False, "error": msg}
            axiom_check = {"passed": False, "skipped": False, "error": msg}
            return GateResult(
                passed=False,
                loc_check=loc_check,
                build_check=build_check,
                axiom_check=axiom_check,
                signature_check=sig_check,
                errors=errors,
            )

        # 2. `lake build` kernel check
        build_cmd = [resolved_lake, "build"]
        if target_modules:
            build_cmd.extend(target_modules)
        rc, out, err = runner(build_cmd, proj_path, env, timeout_s)
        build_passed = rc == 0
        if not build_passed:
            errors.append(f"`{' '.join(build_cmd)}` failed with exit code {rc}: {err.strip() or out.strip()}")
        build_check = {
            "passed": build_passed,
            "skipped": False,
            "command": build_cmd,
            "returncode": rc,
            "stdout_tail": out[-1000:],
            "stderr_tail": err[-1000:],
        }

        # 3. `#print axioms` & `#check` verification for exported declarations
        if exported_decls:
            if not build_passed:
                axiom_check = {
                    "passed": False,
                    "skipped": True,
                    "reason": "Skipped axiom check because `lake build` failed.",
                }
            else:
                script_lines: list[str] = []
                for mod in target_modules or []:
                    script_lines.append(f"import {mod}")
                for decl in exported_decls:
                    script_lines.append(f"#check @{decl}")
                    script_lines.append(f"#print axioms {decl}")
                script_text = "\n".join(script_lines) + "\n"

                with tempfile.NamedTemporaryFile(
                    mode="w",
                    suffix=".lean",
                    prefix="pc_gate_",
                    delete=False,
                    encoding="utf-8",
                ) as tf:
                    tf.write(script_text)
                    tmp_path = Path(tf.name)

                try:
                    check_cmd = [resolved_lake, "env", "lean", str(tmp_path)]
                    arc, aout, aerr = runner(check_cmd, proj_path, env, timeout_s)
                finally:
                    try:
                        tmp_path.unlink(missing_ok=True)
                    except OSError:
                        pass

                combined = f"{aout}\n{aerr}"
                axioms_map = parse_print_axioms(combined)
                sigs_map = parse_check_signatures(combined)

                disallowed: dict[str, list[str]] = {}
                missing_decls: list[str] = []
                for decl in exported_decls:
                    if decl not in axioms_map:
                        missing_decls.append(decl)
                    else:
                        permitted = (
                            set(baseline_axioms[decl])
                            if baseline_axioms is not None and decl in baseline_axioms
                            else allowed
                        )
                        bad = [a for a in axioms_map[decl] if a not in permitted]
                        if bad:
                            disallowed[decl] = bad

                axiom_passed = (arc == 0) and (not missing_decls) and (not disallowed)
                if arc != 0:
                    errors.append(
                        f"Kernel axiom/signature check failed (exit {arc}): {aerr.strip() or aout.strip()}"
                    )
                if missing_decls:
                    errors.append(
                        f"Exported declaration(s) missing from `#print axioms` output: {', '.join(missing_decls)}"
                    )
                if disallowed:
                    details = "; ".join(f"{k}: {v}" for k, v in disallowed.items())
                    errors.append(f"Disallowed axioms detected: {details}")

                axiom_check = {
                    "passed": axiom_passed,
                    "skipped": False,
                    "returncode": arc,
                    "axioms": axioms_map,
                    "missing_decls": missing_decls,
                    "disallowed_axioms": disallowed,
                    "allowed_axioms": sorted(allowed),
                }

                # Optional exact signature check
                if expected_signatures:
                    mismatches: dict[str, dict[str, str]] = {}
                    for decl, exp_sig in expected_signatures.items():
                        got_sig = sigs_map.get(decl)
                        norm_exp = " ".join(exp_sig.split())
                        if got_sig is None or got_sig != norm_exp:
                            mismatches[decl] = {
                                "expected": norm_exp,
                                "actual": got_sig or "<missing>",
                            }
                    sig_passed = len(mismatches) == 0
                    if not sig_passed:
                        errors.append(
                            f"Signature mismatch on {len(mismatches)} declaration(s): {', '.join(mismatches)}"
                        )
                    sig_check = {
                        "passed": sig_passed,
                        "skipped": False,
                        "mismatches": mismatches,
                    }

    all_passed = (
        loc_check.get("passed", False)
        and build_check.get("passed", False)
        and axiom_check.get("passed", False)
        and sig_check.get("passed", False)
        and len(errors) == 0
    )
    return GateResult(
        passed=all_passed,
        loc_check=loc_check,
        build_check=build_check,
        axiom_check=axiom_check,
        signature_check=sig_check,
        errors=errors,
    )
