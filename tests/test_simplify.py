"""Unit and real-`lake` kernel-gate tests for `proof_compressor.refactor.simplify`."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import pytest

from proof_compressor.refactor.gate import (
    STANDARD_LEAN_AXIOMS,
    count_effective_loc,
)
from proof_compressor.refactor.simplify import (
    SimplifyCandidate,
    _build_batch_candidate,
    _parse_print_axioms_safe,
    _run_subprocess_clean,
    count_proof_steps,
    extract_exported_decls,
    find_dead_have_candidates,
    find_mathlib_absorption_candidates,
    find_tactic_collapse_candidates,
    generate_simplify_candidates,
    simplify_module,
    simplify_modules,
    verify_manual_rewrite,
)
from proof_compressor.schema import init_db


def _get_lake_bin() -> str:
    lake = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if not Path(lake).exists():
        pytest.skip("lake binary not installed")
    return lake


def _get_toolchain() -> str:
    tc_dir = Path.home() / ".elan" / "toolchains"
    if tc_dir.exists():
        for child in sorted(tc_dir.iterdir()):
            if "v4." in child.name:
                ver = child.name.split("---")[-1]
                return f"leanprover/lean4:{ver}\n"
    return "leanprover/lean4:v4.34.1\n"


def _write_lean_project(root: Path, files: dict[str, str], lib_name: str = "Demo") -> None:
    (root / "lean-toolchain").write_text(_get_toolchain(), encoding="utf-8")
    (root / "lakefile.toml").write_text(
        f'name = "simplify_test"\n\n[[lean_lib]]\nname = "{lib_name}"\n',
        encoding="utf-8",
    )
    for rel, content in files.items():
        fpath = root / rel
        fpath.parent.mkdir(parents=True, exist_ok=True)
        fpath.write_text(content, encoding="utf-8")


# ---------------------------------------------------------------------------
# Unit tests: metrics, exported decls, dead-binding & tactic collapses
# ---------------------------------------------------------------------------


def test_count_proof_steps_and_extract_exported_decls() -> None:
    src = """\
namespace Demo

/-
block comment with := by exact foo
-/
private lemma helper_priv (n : Nat) : n = n := by
  -- inline comment
  rfl

@[simp]
theorem C2' (n : Nat) : n + 0 = n := by
  rw [Nat.add_zero]

def myId (n : Nat) : Nat := n

instance : Inhabited Nat := ⟨0⟩

theorem chained (a b : Nat) (h : a = b) : b = a := by
  subst h; rfl

end Demo
"""
    # helper_priv (1: rfl) + C2' (1: rw) + chained (2: subst h; rfl) = 4
    assert count_proof_steps(src) == 4

    decls = extract_exported_decls(src, "Demo.Test")
    assert "Demo.C2'" in decls
    assert "Demo.myId" in decls
    assert "Demo.chained" in decls
    assert all("helper_priv" not in d for d in decls)


def test_prune_dead_have_let_set_and_private_guards() -> None:
    src = """\
namespace Demo

private lemma orphan_priv : 1 = 1 := by
  rfl

@[simp]
private lemma tagged_simp : 0 + 1 = 1 := by
  rfl

private lemma referenced_priv : 2 = 2 := by
  rfl

theorem sample (n : Nat) : 2 = 2 := by
  have h_dead : 1 = 1 := rfl
  let dead_let := n + 1
  set dead_set := n + 2
  set used_alias := n + 3 with h_used_alias
  have this : 3 = 3 := rfl
  have instFake : 4 = 4 := rfl
  have h_used := referenced_priv
  have _check : used_alias = n + 3 := h_used_alias
  exact h_used

end Demo
"""
    cands = find_dead_have_candidates(src, "Demo.Sample")
    rules_and_descs = [(c.rule, c.description, c.priority) for c in cands]

    assert any(r == "prune_dead_private" and "orphan_priv" in d for r, d, _ in rules_and_descs)
    assert not any("tagged_simp" in d for _, d, _ in rules_and_descs)
    assert not any("referenced_priv" in d for _, d, _ in rules_and_descs)

    assert any(r == "prune_dead_have" and "h_dead" in d for r, d, _ in rules_and_descs)
    assert any(r == "prune_dead_let" and "dead_let" in d for r, d, _ in rules_and_descs)
    assert any(r == "prune_dead_set" and "dead_set" in d for r, d, _ in rules_and_descs)
    # `used_alias` is kept because `h_used_alias` from `with h_used_alias` is referenced
    assert not any("used_alias" in d for _, d, _ in rules_and_descs)
    # `this`, `inst*`, and `h_used` must not be pruned
    assert not any("`have this`" in d for _, d, _ in rules_and_descs)
    assert not any("instFake" in d for _, d, _ in rules_and_descs)
    assert not any("h_used" in d for _, d, _ in rules_and_descs)


def test_dead_have_lowers_priority_before_context_tactic() -> None:
    src = """\
theorem arith_ctx (n : Nat) (hn : n > 0) : n ≥ 1 := by
  have h_aux : 0 < n := hn
  omega
"""
    cands = find_dead_have_candidates(src, "Demo.Ctx")
    have_cands = [c for c in cands if c.rule == "prune_dead_have"]
    assert len(have_cands) == 1
    assert have_cands[0].priority == 35


def test_tactic_collapse_rules_and_multiline_first() -> None:
    src = """\
theorem t_have_this (P : Prop) (hp : P) : P := by
  have := hp
  exact this

theorem t_have_exact (P : Prop) (hp : P) : P := by
  have hx := hp
  exact hx

theorem t_have_simpa (P : Prop) (hp : P) : P := by
  have hx := hp
  simpa using hx

theorem t_first_single (n : Nat) : n = n := by
  first
    | rfl
    | simp

theorem t_first_multiline (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  first
    | (refine ⟨?_, ?_⟩
       · exact hp
       · exact hq)
    | trivial

theorem t_by_exact (n : Nat) : n = n := by
  exact rfl

theorem t_bare_bullet (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  ·
    exact hp
  ·
    exact hq

theorem t_rw_chain (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  rw [h2]

theorem t_not_by_exact (a b : Nat) (h : a = b) : a = b := by
  exact h
  -- trailing tactic below prevents collapse_by_exact if indented at same level
"""
    cands = find_tactic_collapse_candidates(src, "Demo.Collapse")
    by_rule: dict[str, list[SimplifyCandidate]] = {}
    for c in cands:
        by_rule.setdefault(c.rule, []).append(c)

    assert "collapse_have_this" in by_rule
    assert any("  exact hp" in c.new_source for c in by_rule["collapse_have_this"])

    assert "collapse_have_exact" in by_rule
    assert any("  exact hp" in c.new_source for c in by_rule["collapse_have_exact"])

    assert "collapse_have_simpa" in by_rule
    assert any("  simpa using hp" in c.new_source for c in by_rule["collapse_have_simpa"])

    assert "collapse_by_exact" in by_rule
    assert any(":= rfl" in c.new_source for c in by_rule["collapse_by_exact"])

    assert "collapse_bare_bullet" in by_rule
    assert any("  · exact hp" in c.new_source for c in by_rule["collapse_bare_bullet"])

    assert "merge_rw_chain" in by_rule
    assert any("  rw [h1, h2]" in c.new_source for c in by_rule["merge_rw_chain"])

    first_cands = by_rule.get("collapse_first_branch", [])
    assert len(first_cands) >= 4
    # Multi-line parenthesized branch strips outer `(` and `)` and preserves relative indent
    multiline_hits = [
        c for c in first_cands if "  refine ⟨?_, ?_⟩\n  · exact hp\n  · exact hq" in c.new_source
    ]
    assert multiline_hits


def test_by_exact_not_collapsed_when_followed_by_same_indent_tactic() -> None:
    src = """\
theorem two_steps (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  exact hp
  exact hq
"""
    # Here `:= by` is followed by `constructor`, not `exact`; verify non-collapse
    cands = find_tactic_collapse_candidates(src, "Demo.NoCollapse")
    assert not any(c.rule == "collapse_by_exact" for c in cands)

    # Even if first tactic is `exact`, a following same-indent tactic must block collapse
    src2 = """\
theorem two_exacts (P : Prop) (hp : P) : P := by
  exact hp
  done
"""
    cands2 = find_tactic_collapse_candidates(src2, "Demo.NoCollapse2")
    assert not any(c.rule == "collapse_by_exact" for c in cands2)


def test_batch_high_confidence_and_generate_dedup() -> None:
    src = """\
theorem batch_target (P : Prop) (hp : P) : P := by
  have unused : 1 = 1 := rfl
  have := hp
  exact this

theorem wrapper (n : Nat) : n = n := by
  rfl
"""
    batch = _build_batch_candidate(src, "Demo.Batch")
    assert batch is not None
    assert batch.rule == "batch_high_confidence"
    assert batch.loc_saved_est >= 2
    assert count_effective_loc(batch.new_source) <= count_effective_loc(src) - 2

    all_cands = generate_simplify_candidates(src, "Demo.Batch")
    assert all_cands[0].rule == "batch_high_confidence"
    sources = [c.new_source for c in all_cands]
    assert len(sources) == len(set(sources))
    assert all(
        count_effective_loc(c.new_source) < count_effective_loc(src) for c in all_cands
    )


def test_mathlib_absorption_from_db_and_patterns(tmp_path: Path) -> None:
    from proof_compressor.ingest.lean_parser import parse_lean_source

    helper_src = """\
private theorem my_zero_helper (a : Nat) : a = a := by
  have h : 0 = 0 := rfl
  rfl

theorem client (n : Nat) : n = n := by
  exact my_zero_helper n

theorem sum_zero_pattern (s : Finset Nat) (h : ∀ x ∈ s, (0 : Nat) = 0) : ∑ x ∈ s, (0 : Nat) = 0 := by
  simp
  rfl
"""
    parsed = parse_lean_source(helper_src, "Demo.Absorb")
    priv_decl = next(d for d in parsed.declarations if d.short_name == "my_zero_helper")

    db_path = tmp_path / "mathlib.db"
    conn = init_db(db_path)
    conn.execute(
        "INSERT INTO modules (path, package, loc, is_mathlib) VALUES (?, ?, ?, ?)",
        ("Mathlib.Init", "mathlib", 10, 1),
    )
    mod_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
    conn.execute(
        """
        INSERT INTO declarations
            (name, short_name, module_id, kind, type_sig, canonical_type_hash, body_loc, is_mathlib, is_bookkeeping)
        VALUES (?, ?, ?, ?, ?, ?, ?, 1, 0)
        """,
        (
            "Mathlib.Fake.eq_refl",
            "eq_refl",
            mod_id,
            "theorem",
            priv_decl.type_sig,
            priv_decl.canonical_type_hash,
            1,
        ),
    )
    conn.commit()
    conn.close()

    cands = find_mathlib_absorption_candidates(helper_src, "Demo.Absorb", db_path=db_path)
    assert any(
        c.rule == "absorb_mathlib_inline" and "Mathlib.Fake.eq_refl" in c.new_source
        for c in cands
    )
    assert any(
        c.rule == "absorb_mathlib_helper" and "Mathlib.Fake.eq_refl" in c.new_source
        for c in cands
    )
    assert any(
        c.rule == "absorb_mathlib_helper" and "Finset.sum_eq_zero" in c.new_source
        for c in cands
    )


# ---------------------------------------------------------------------------
# Unit tests: primed identifier axioms, killpg timeout, mocked gate & revert
# ---------------------------------------------------------------------------


def test_parse_print_axioms_safe_handles_primed_identifiers() -> None:
    lean_output = """\
'Demo.C2'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Demo.p'' does not depend on any axioms
'Demo.plain' depends on axioms: [propext]
"""
    parsed = _parse_print_axioms_safe(lean_output)
    assert parsed["Demo.C2'"] == ["propext", "Classical.choice", "Quot.sound"]
    assert parsed["Demo.p'"] == []
    assert parsed["Demo.plain"] == ["propext"]


def test_run_subprocess_clean_kills_process_group_on_timeout(tmp_path: Path) -> None:
    pid_file = tmp_path / "child.pid"
    script = (
        "import subprocess, sys, time; "
        "p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
        f"open({str(pid_file)!r}, 'w').write(str(p.pid)); "
        "time.sleep(60)"
    )
    rc, _out, err = _run_subprocess_clean(
        [sys.executable, "-c", script],
        cwd=tmp_path,
        env=dict(os.environ),
        timeout_s=1,
    )
    assert rc == 124
    assert "timed out" in err.lower()
    assert pid_file.exists()
    child_pid = int(pid_file.read_text(encoding="utf-8").strip())

    # Wait briefly for OS to reap the SIGKILLed child from the process group
    deadline = time.monotonic() + 3.0
    alive = True
    while time.monotonic() < deadline:
        try:
            os.kill(child_pid, 0)
        except ProcessLookupError:
            alive = False
            break
        time.sleep(0.05)
    assert not alive, f"Orphan child PID {child_pid} survived killpg timeout!"


def test_simplify_module_mock_gate_reverts_failures_and_handles_dry_run(tmp_path: Path) -> None:
    # Missing module reports failure cleanly
    missing = simplify_module(tmp_path, "Demo.DoesNotExist", dry_run=True)
    assert missing.gate_passed is False
    assert missing.errors

    sample_src = """\
namespace Demo

theorem C2' (n : Nat) : n + 0 = n := by
  have unused : 1 = 1 := rfl
  exact Nat.add_zero n

end Demo
"""
    mod_file = tmp_path / "src" / "Demo" / "MockMod.lean"
    mod_file.parent.mkdir(parents=True, exist_ok=True)
    mod_file.write_text(sample_src, encoding="utf-8")

    # Reject every candidate edit via mocked `lake build` failure and verify revert on disk
    def failing_edit_runner(
        cmd: list[str], cwd: Path, env: dict[str, str], timeout_s: int
    ) -> tuple[int, str, str]:
        if cmd[:2] == ["lake", "build"]:
            cur = mod_file.read_text(encoding="utf-8")
            if cur == sample_src:
                return 0, "", ""
            return 1, "", "simulated type error after rewrite"
        if cmd[:3] == ["lake", "env", "lean"]:
            return (
                0,
                "Demo.C2' : ∀ (n : Nat), n + 0 = n\n"
                "'Demo.C2'' depends on axioms: [propext]\n",
                "",
            )
        return 1, "", f"unexpected cmd: {cmd}"

    res_reverted = simplify_module(
        tmp_path,
        "Demo.MockMod",
        lake_bin="lake",
        max_candidates=5,
        command_runner=failing_edit_runner,
    )
    assert res_reverted.gate_passed is True
    assert res_reverted.changed is False
    assert len(res_reverted.rejected_edits) >= 1
    assert mod_file.read_text(encoding="utf-8") == sample_src
    assert res_reverted.axioms.get("Demo.C2'") == ["propext"]

    # verify_manual_rewrite rejects non-standard axioms / failed build and reverts file
    ok_manual, gate_manual, _, _, _ = verify_manual_rewrite(
        tmp_path,
        "Demo.MockMod",
        "namespace Demo\ntheorem C2' (n : Nat) : n + 0 = n := by sorry\nend Demo\n",
        lake_bin="lake",
        command_runner=failing_edit_runner,
    )
    assert ok_manual is False
    assert not gate_manual.passed
    assert mod_file.read_text(encoding="utf-8") == sample_src

    # dry_run=True applies deterministic rewrites via simplify_modules
    dry_results = simplify_modules(tmp_path, ["Demo.MockMod"], dry_run=True, max_rounds=2)
    assert len(dry_results) == 1
    assert dry_results[0].changed is True
    assert dry_results[0].loc_saved >= 1


# ---------------------------------------------------------------------------
# Real Lean 4 + `lake` end-to-end kernel-gate tests
# ---------------------------------------------------------------------------


def test_real_lake_simplify_module_and_verify_manual_rewrite(tmp_path: Path) -> None:
    lake = _get_lake_bin()

    original_src = """\
namespace Demo

private theorem dead_helper (n : Nat) : n = n := by
  rfl

theorem C2' (n : Nat) : n + 0 = n := by
  have dead_h : 1 = 1 := rfl
  have := Nat.add_zero n
  exact this

theorem first_test (P : Prop) : P → P := by
  first
    | (intro h
       exact h)
    | simp

theorem first_multiline_test (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  first
    | (constructor
       · exact hp
       · exact hq)
    | sorry

theorem by_exact_test (a b : Nat) (h : a = b) : a = b := by
  exact h

theorem manual_target (f : Nat → Nat) (hf : ∀ x, f x = f (x + 1)) (n : Nat) :
    f n = f (n + 2) := by
  have h1 : f n = f (n + 1) := hf n
  have h2 : f (n + 1) = f (n + 2) := hf (n + 1)
  exact Eq.trans h1 h2

end Demo
"""
    _write_lean_project(tmp_path, {"Demo/Sample.lean": original_src})
    sample_path = tmp_path / "Demo" / "Sample.lean"

    res = simplify_module(
        tmp_path,
        "Demo.Sample",
        file_path=sample_path,
        lake_bin=lake,
        timeout_s=120,
        max_candidates=25,
        max_rounds=6,
    )

    assert res.gate_passed is True, f"errors={res.errors}"
    assert res.changed is True
    assert res.before_loc > res.after_loc
    assert res.loc_saved >= 5
    assert res.before_steps > res.after_steps
    assert "Demo.C2'" in res.baseline_signatures
    assert "Demo.C2'" in res.axioms
    for decl_name, axs in res.axioms.items():
        assert set(axs) <= STANDARD_LEAN_AXIOMS, f"{decl_name} used non-standard axioms: {axs}"
    assert len(res.accepted_edits) >= 1
    assert "dead_helper" not in sample_path.read_text(encoding="utf-8")

    simplified_src = sample_path.read_text(encoding="utf-8")
    assert "exact Eq.trans h1 h2" in simplified_src

    # Attempt an invalid manual rewrite (`sorry`) -> must fail gate and revert to `simplified_src`
    broken_src = simplified_src.replace("exact Eq.trans h1 h2", "sorry")
    assert broken_src != simplified_src
    ok_bad, gate_bad, _, _, _ = verify_manual_rewrite(
        tmp_path,
        "Demo.Sample",
        broken_src,
        file_path=sample_path,
        lake_bin=lake,
        timeout_s=120,
    )
    assert ok_bad is False
    assert not gate_bad.passed
    assert sample_path.read_text(encoding="utf-8") == simplified_src

    # Apply a genuine manual term-mode rewrite collapsing `manual_target`
    manual_shorter = simplified_src.replace(
        "    f n = f (n + 2) := by\n"
        "  have h1 : f n = f (n + 1) := hf n\n"
        "  have h2 : f (n + 1) = f (n + 2) := hf (n + 1)\n"
        "  exact Eq.trans h1 h2",
        "    f n = f (n + 2) := Eq.trans (hf n) (hf (n + 1))",
    )
    assert count_effective_loc(manual_shorter) < count_effective_loc(simplified_src)

    ok_good, gate_good, base_sigs, manual_axioms, elapsed = verify_manual_rewrite(
        tmp_path,
        "Demo.Sample",
        manual_shorter,
        file_path=sample_path,
        lake_bin=lake,
        timeout_s=120,
    )
    assert ok_good is True, f"Manual rewrite failed: {gate_good.errors}"
    assert gate_good.passed is True
    assert elapsed > 0.0
    assert "Demo.manual_target" in base_sigs
    assert "Demo.C2'" in manual_axioms
    for decl_name, axs in manual_axioms.items():
        assert set(axs) <= STANDARD_LEAN_AXIOMS, f"{decl_name} non-standard axioms: {axs}"

    # Final clean `lake build Demo.Sample` check after all edits
    proc = subprocess.run(
        [lake, "build", "Demo.Sample"],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stderr or proc.stdout
