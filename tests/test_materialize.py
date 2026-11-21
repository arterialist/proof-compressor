"""Ground-truth Lean 4 compilation and soundness tests for proof_compressor.analyze.materialize."""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

from proof_compressor.analyze import run_analysis
from proof_compressor.analyze.materialize import (
    materialize_project,
)
from proof_compressor.cli import main as cli_main
from proof_compressor.ingest.stream_archive import ingest_source
from proof_compressor.refactor.gate import (
    count_files_effective_loc,
    verify_refactor_gate,
)


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


@pytest.fixture
def compilable_lean_project(tmp_path: Path) -> Path:
    """Create a multi-module Lean 4 project with:
    - `Core.Types`: core typeclass `HasWeight`, structure `Packet`, needed theorem, and dead theorem
    - `Core.Instances`: implicit `instance instHasWeightPacket : HasWeight Packet` (never referenced
      by identifier name in `Main.lean`!) + dead theorem
    - `Core.Barrel`: zero-declaration barrel importing `Core.Types`, `Core.Instances`, and `Dead.Unused`
    - `Dead.Unused`: completely unused module with dead definitions and theorems
    - `Main`: imports `Core.Barrel` and `Dead.Unused`, uses `[HasWeight Packet]` implicitly via
      typeclass synthesis to prove `main_weight_theorem`, plus an unused intra-module theorem
    """
    proj = tmp_path / "orig_lean_proj"
    (proj / "src" / "Core").mkdir(parents=True)
    (proj / "src" / "Dead").mkdir(parents=True)

    (proj / "lean-toolchain").write_text(_get_toolchain(), encoding="utf-8")
    (proj / "lakefile.toml").write_text(
        'name = "prunedemo"\n'
        'srcDir = "src"\n'
        'defaultTargets = ["Main"]\n\n'
        '[[lean_lib]]\n'
        'name = "Core"\n'
        'globs = ["Core.+"]\n\n'
        '[[lean_lib]]\n'
        'name = "Dead"\n'
        'globs = ["Dead.+"]\n\n'
        '[[lean_lib]]\n'
        'name = "Main"\n'
        'roots = ["Main"]\n',
        encoding="utf-8",
    )

    (proj / "src" / "Core" / "Types.lean").write_text(
        """\
namespace Core

class HasWeight (α : Type) where
  weight : α → Nat

structure Packet where
  payload : Nat

theorem packet_payload_nonneg (p : Packet) : 0 ≤ p.payload :=
  Nat.zero_le p.payload

/-- Dead intra-module lemma in Core.Types that should be stripped. -/
theorem dead_types_lemma (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

end Core
""",
        encoding="utf-8",
    )

    (proj / "src" / "Core" / "Instances.lean").write_text(
        """\
import Core.Types

namespace Core

instance instHasWeightPacket : HasWeight Packet where
  weight p := p.payload

/-- Dead intra-module lemma in Core.Instances that should be stripped. -/
theorem dead_instance_helper (k : Nat) : k = k := by
  rfl

end Core
""",
        encoding="utf-8",
    )

    (proj / "src" / "Core" / "Barrel.lean").write_text(
        """\
import Core.Types
import Core.Instances
import Dead.Unused
""",
        encoding="utf-8",
    )

    (proj / "src" / "Dead" / "Unused.lean").write_text(
        """\
namespace Dead

def unusedHelper (x : Nat) : Nat := x + 99

theorem unused_dead_theorem (x : Nat) : unusedHelper x = x + 99 := by
  rfl

end Dead
""",
        encoding="utf-8",
    )

    (proj / "src" / "Main.lean").write_text(
        """\
import Core.Barrel
import Dead.Unused

open Core

def evalWeight {α : Type} [HasWeight α] (x : α) : Nat :=
  HasWeight.weight x

/-- Root target theorem relying on implicit typeclass synthesis of `instHasWeightPacket`. -/
theorem main_weight_theorem (p : Packet) : 0 ≤ evalWeight p := by
  change 0 ≤ p.payload
  exact packet_payload_nonneg p

/-- Dead intra-module theorem in Main that should be stripped. -/
theorem main_dead_extra (a b : Nat) : a + b = a + b := by
  rfl
""",
        encoding="utf-8",
    )
    return proj


def test_materialize_decl_exact_breaks_implicit_instance_while_instance_aware_compiles(
    compilable_lean_project: Path, tmp_path: Path
) -> None:
    """Verify with real `lake build` + `#print axioms`:
    1. Naive `decl-exact` pruning drops `Core.Instances` (since `instHasWeightPacket` is never
       mentioned by identifier name), causing `lake build` to fail on typeclass synthesis.
    2. `instance-aware` pruning keeps `Core.Instances`, drops `Dead.Unused`, strips dead
       intra-module theorems (`dead_types_lemma`, `dead_instance_helper`, `main_dead_extra`),
       rewrites imports, compiles cleanly with `lake build`, and passes `verify_refactor_gate`!
    """
    lake_bin = _get_lake_bin()
    env = os.environ.copy()
    elan_bin = str(Path.home() / ".elan" / "bin")
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

    db_path = tmp_path / "proj.db"
    ingest_source(compilable_lean_project, db_path)
    run_analysis(db_path, roots=["main_weight_theorem"])

    orig_files = list((compilable_lean_project / "src").rglob("*.lean"))
    orig_loc = count_files_effective_loc(orig_files)

    # 1. Materialize with naive `decl-exact` mode
    out_exact = tmp_path / "mat_decl_exact"
    rep_exact = materialize_project(
        db_path,
        source=compilable_lean_project,
        output_dir=out_exact,
        roots=["main_weight_theorem"],
        mode="decl-exact",
    )
    assert rep_exact.kept_modules == 2  # Only Main and Core.Types
    assert not (out_exact / "src" / "Core" / "Instances.lean").exists()
    assert not (out_exact / "src" / "Dead" / "Unused.lean").exists()

    proc_exact = subprocess.run(
        [lake_bin, "build", "Main"],
        cwd=out_exact,
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert proc_exact.returncode != 0, "Expected naive decl-exact build to fail without Core.Instances"
    assert "HasWeight" in (proc_exact.stdout + proc_exact.stderr)

    # 2. Materialize with `instance-aware` mode (via CLI to test CLI wiring too!)
    out_inst = tmp_path / "mat_instance_aware"
    rc = cli_main(
        [
            "materialize",
            str(db_path),
            "--source",
            str(compilable_lean_project),
            "--out",
            str(out_inst),
            "--roots",
            "main_weight_theorem",
            "--mode",
            "instance-aware",
        ]
    )
    assert rc == 0

    # Dead module must be completely dropped
    assert not (out_inst / "src" / "Dead" / "Unused.lean").exists()
    # Instance module and Types module must be kept
    assert (out_inst / "src" / "Core" / "Types.lean").exists()
    assert (out_inst / "src" / "Core" / "Instances.lean").exists()
    assert (out_inst / "src" / "Main.lean").exists()

    # Dead intra-module theorems and dead imports must be stripped from kept files
    main_txt = (out_inst / "src" / "Main.lean").read_text(encoding="utf-8")
    types_txt = (out_inst / "src" / "Core" / "Types.lean").read_text(encoding="utf-8")
    inst_txt = (out_inst / "src" / "Core" / "Instances.lean").read_text(encoding="utf-8")

    assert "Dead.Unused" not in main_txt
    assert "main_dead_extra" not in main_txt
    assert "dead_types_lemma" not in types_txt
    assert "dead_instance_helper" not in inst_txt

    pruned_files = list((out_inst / "src").rglob("*.lean"))
    pruned_loc = count_files_effective_loc(pruned_files)
    assert pruned_loc < orig_loc

    # Verify with Stage 4 kernel verification gate (`lake build Main` + `#print axioms` + LOC reduction)
    gate = verify_refactor_gate(
        out_inst,
        target_modules=["Main"],
        exported_decls=["main_weight_theorem"],
        before_loc=orig_loc,
        after_loc=pruned_loc,
        run_lake=True,
        lake_bin=lake_bin,
    )
    assert gate.passed is True, f"Verification gate failed on instance-aware materialized project: {gate.errors}"
    assert gate.build_check["passed"] is True
    assert gate.axiom_check["passed"] is True
    assert gate.axiom_check["axioms"].get("main_weight_theorem") == []


def test_materialize_real_alpo_rh_slice_compiles_with_lake(tmp_path: Path) -> None:
    """Extract verbatim pure-Lean modules from `data/lean.tar.gz.part01` (`BuildAid.D1..D3`,
    `Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports`,
    `Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct`), materialize a pruned project,
    and verify it compiles with real `~/.elan/bin/lake build` and `#print axioms`.
    """
    repo_root = Path(__file__).resolve().parent.parent
    part01 = repo_root / "data" / "lean.tar.gz.part01"
    if not part01.exists():
        pytest.skip("data/lean.tar.gz.part01 not present")

    lake_bin = _get_lake_bin()
    from proof_compressor.ingest.lean_parser import normalize_module_path
    from proof_compressor.ingest.stream_archive import iter_lean_sources

    real_targets = {
        "BuildAid.D1",
        "BuildAid.D2",
        "BuildAid.D3",
        "Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports",
        "Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct",
    }
    extracted: dict[str, tuple[str, str]] = {}
    for raw_path, text in iter_lean_sources(part01):
        mod, _, _ = normalize_module_path(raw_path)
        if mod in real_targets:
            extracted[mod] = (raw_path, text)
            if len(extracted) == len(real_targets):
                break

    assert len(extracted) == len(real_targets)

    slice_proj = tmp_path / "alpo_slice_orig"
    (slice_proj / "src").mkdir(parents=True)
    (slice_proj / "lean-toolchain").write_text(_get_toolchain(), encoding="utf-8")
    (slice_proj / "lakefile.toml").write_text(
        'name = "alpo_slice"\n'
        'srcDir = "src"\n'
        'defaultTargets = ["AlpoDriver"]\n\n'
        '[[lean_lib]]\n'
        'name = "BuildAid"\n'
        'globs = ["BuildAid.+"]\n\n'
        '[[lean_lib]]\n'
        'name = "Formalism"\n'
        'globs = ["Formalism.+"]\n\n'
        '[[lean_lib]]\n'
        'name = "AlpoDriver"\n'
        'roots = ["AlpoDriver"]\n',
        encoding="utf-8",
    )

    for mod, (raw_path, text) in extracted.items():
        rel = raw_path[len("lean/") :] if raw_path.startswith("lean/") else raw_path
        dest = slice_proj / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text, encoding="utf-8")

    (slice_proj / "src" / "AlpoDriver.lean").write_text(
        """\
import BuildAid.D1
import BuildAid.D2
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct

namespace Formalism

structure PairBox where
  fst : Nat
  snd : Nat

end Formalism

theorem alpo_tactic_soundness (a b : Nat) :
    a = a ∧ b = b := by
  kexactB (And.intro (@rfl Nat a) (@rfl Nat b))

theorem alpo_kcopy_soundness (P Q : Prop) (h : P ∧ Q) : P ∧ Q := by
  kcopy h

theorem dead_driver_lemma : 1 + 1 = 2 := rfl
""",
        encoding="utf-8",
    )

    db_path = tmp_path / "alpo_slice.db"
    ingest_source(slice_proj, db_path)
    run_analysis(db_path, roots=["alpo_tactic_soundness", "alpo_kcopy_soundness"])

    out_mat = tmp_path / "alpo_slice_pruned"
    rep = materialize_project(
        db_path,
        source=slice_proj,
        output_dir=out_mat,
        roots=["alpo_tactic_soundness", "alpo_kcopy_soundness"],
        mode="import-closure",
        strip_dead_decls=True,
        rewrite_imports=True,
    )

    assert not (out_mat / "src" / "BuildAid" / "D3.lean").exists()
    driver_pruned = (out_mat / "src" / "AlpoDriver.lean").read_text(encoding="utf-8")
    assert "dead_driver_lemma" not in driver_pruned
    assert rep.stripped_intra_module_declarations >= 1

    orig_loc = count_files_effective_loc(list((slice_proj / "src").rglob("*.lean")))
    pruned_loc = count_files_effective_loc(list((out_mat / "src").rglob("*.lean")))

    gate = verify_refactor_gate(
        out_mat,
        target_modules=["AlpoDriver"],
        exported_decls=["alpo_tactic_soundness", "alpo_kcopy_soundness"],
        before_loc=orig_loc,
        after_loc=pruned_loc,
        run_lake=True,
        lake_bin=lake_bin,
    )
    assert gate.passed is True, f"Real alpo.ge slice failed verification gate: {gate.errors}"
    assert gate.axiom_check["axioms"].get("alpo_tactic_soundness") == []
    assert gate.axiom_check["axioms"].get("alpo_kcopy_soundness") == []


def test_materialize_real_alpo_main_supplements_spine_compiles_with_lake(tmp_path: Path) -> None:
    """Extract the verbatim top-level `alpo.ge` spine (`Main.lean`, `Supplements.Kernels.MainTheoremsAll`,
    `Supplements.Kernels.MainTheoremsCritical`, `Supplements.Kernels.MainTheorems`), pair with
    minimal interface modules for `Statements` / `CritLine` / `ClaimStrip` / `MainConclusion` and
    the 4 dead `SmallClassNumbers.*` side-imports in `MainTheoremsAll`/`MainTheoremsCritical`,
    run `materialize_project(mode="instance-aware")`, and verify:
    1. All 4 dead `SmallClassNumbers.*` modules and their import lines in `MainTheoremsAll` /
       `MainTheoremsCritical` are automatically pruned!
    2. All 5 verbatim root theorems in `Main.lean` (`riemannHypothesis`, `riemannZeta_eq_zero_re`,
       `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`)
       compile cleanly with `~/.elan/bin/lake build` and pass `#print axioms`!
    """
    repo_root = Path(__file__).resolve().parent.parent
    part01 = repo_root / "data" / "lean.tar.gz.part01"
    if not part01.exists():
        pytest.skip("data/lean.tar.gz.part01 not present")

    lake_bin = _get_lake_bin()
    from proof_compressor.ingest.lean_parser import normalize_module_path
    from proof_compressor.ingest.stream_archive import iter_lean_sources

    verbatim_targets = {
        "Main",
        "Supplements.Kernels.MainTheoremsAll",
        "Supplements.Kernels.MainTheoremsCritical",
        "Supplements.Kernels.MainTheorems",
    }
    extracted: dict[str, tuple[str, str]] = {}
    for raw_path, text in iter_lean_sources(part01):
        mod, _, _ = normalize_module_path(raw_path)
        if mod in verbatim_targets:
            extracted[mod] = (raw_path, text)
            if len(extracted) == len(verbatim_targets):
                break

    assert len(extracted) == len(verbatim_targets)

    spine_proj = tmp_path / "alpo_spine_orig"
    (spine_proj / "src").mkdir(parents=True)
    (spine_proj / "lean-toolchain").write_text(_get_toolchain(), encoding="utf-8")
    (spine_proj / "lakefile.toml").write_text(
        'name = "alpo_spine"\n'
        'srcDir = "src"\n'
        'defaultTargets = ["Main"]\n\n'
        '[[lean_lib]]\n'
        'name = "Development"\n'
        'globs = ["Development.+"]\n\n'
        '[[lean_lib]]\n'
        'name = "Formalism"\n'
        'globs = ["Formalism.+"]\n\n'
        '[[lean_lib]]\n'
        'name = "Supplements"\n'
        'globs = ["Supplements.+"]\n\n'
        '[[lean_lib]]\n'
        'name = "Main"\n'
        'roots = ["Statements", "Main"]\n',
        encoding="utf-8",
    )

    # Write verbatim Main.lean and Supplements.Kernels.MainTheorems*
    for mod, (raw_path, text) in extracted.items():
        rel = raw_path[len("lean/") :] if raw_path.startswith("lean/") else raw_path
        dest = spine_proj / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text, encoding="utf-8")

    # Minimal self-contained Mathlib/Statements/upstream interface matching the exact signatures
    # consumed by verbatim `Supplements.Kernels.MainTheorems` and `Main.lean`
    (spine_proj / "src" / "Statements.lean").write_text(
        """\
abbrev ℕ := Nat

structure ℂ where
  re : Int
  im : Int

instance : OfNat ℂ 0 where ofNat := ⟨0, 0⟩
instance : OfNat ℂ 1 where ofNat := ⟨1, 0⟩
instance : OfNat Int 1 where ofNat := 1
instance : OfNat Int 2 where ofNat := 2
instance : HDiv Int Int Int where hDiv a b := a / b

namespace Complex
end Complex

structure DirichletCharacter (α : Type) (N : ℕ) where
  level : ℕ := N

namespace DirichletCharacter
def IsPrimitive {α : Type} {N : ℕ} (_χ : DirichletCharacter α N) : Prop := True
def LFunction {N : ℕ} (_χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ⟨s.re - (1 / 2 : Int), 0⟩
end DirichletCharacter

def riemannZeta (s : ℂ) : ℂ := ⟨s.re - (1 / 2 : Int), 0⟩

def RiemannHypothesis : Prop := ∀ s : ℂ, riemannZeta s = 0 → s.re = 1 / 2
def RiemannZetaZerosOnLine : Prop := RiemannHypothesis
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    (1 / 2 : Int) < s.re → DirichletCharacter.LFunction χ s ≠ 0
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    (0 : Int) < s.re → s.re < (1 : Int) → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, (0 : Int) < s.re → s.re < (1 : Int) → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
""",
        encoding="utf-8",
    )

    crit_path = spine_proj / "src" / "Formalism" / "GammaFactorNonvanishing" / "CritLine.lean"
    crit_path.parent.mkdir(parents=True, exist_ok=True)
    crit_path.write_text(
        """\
import Statements

namespace UpperTheory
abbrev EveryCharacter : Prop := DirichletLNonvanishingRightOfHalf
end UpperTheory

namespace Formalism.VW

theorem rh_of_every (_h : UpperTheory.EveryCharacter) : RiemannHypothesis := by
  intro s hs
  have h1 : s.re - (1 / 2 : Int) = 0 := congrArg ℂ.re hs
  omega

theorem critLine (_h : UpperTheory.EveryCharacter) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (_hχ : χ.IsPrimitive) (s : ℂ)
    (_h0 : (0 : Int) < s.re) (_h1 : s.re < (1 : Int))
    (hz : DirichletCharacter.LFunction χ s = 0) : s.re = 1 / 2 := by
  have h2 : s.re - (1 / 2 : Int) = 0 := congrArg ℂ.re hz
  omega

end Formalism.VW
""",
        encoding="utf-8",
    )

    strip_path = spine_proj / "src" / "Development" / "AutomorphicArithmetic" / "CharacterBoxes" / "ClaimStrip.lean"
    strip_path.parent.mkdir(parents=True, exist_ok=True)
    strip_path.write_text(
        """\
import Formalism.GammaFactorNonvanishing.CritLine

namespace Claim
abbrev HalfPlane : Prop := UpperTheory.EveryCharacter
abbrev Strip : Prop := DirichletLZerosOnLine
abbrev Zeta : Prop := RiemannZetaZerosOnLine

theorem strip (_h : HalfPlane) : Strip := by
  intro N _ χ s _ _ hz
  have h2 : s.re - (1 / 2 : Int) = 0 := congrArg ℂ.re hz
  omega

theorem zeta (h : HalfPlane) : Zeta := Formalism.VW.rh_of_every h

theorem dead_zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl
end Claim
""",
        encoding="utf-8",
    )

    mc_path = spine_proj / "src" / "Development" / "AutomorphicArithmetic" / "CharacterBoxes" / "MainConclusion.lean"
    mc_path.parent.mkdir(parents=True, exist_ok=True)
    mc_path.write_text(
        """\
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip

theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter := by
  intro N _ χ s hgt hz
  have h2 : s.re - (1 / 2 : Int) = 0 := congrArg ℂ.re hz
  omega
""",
        encoding="utf-8",
    )

    # Write the 4 dead SmallClassNumbers side-modules imported by verbatim MainTheoremsAll & MainTheoremsCritical
    sc_dir = spine_proj / "src" / "Development" / "AutomorphicArithmetic" / "AutomorphicVarieties" / "SmallClassNumbers"
    sc_dir.mkdir(parents=True, exist_ok=True)
    for sc_name in ("CorGKOf", "ClassNumberThree", "LenEqZeroIff", "OnePoint"):
        (sc_dir / f"{sc_name}.lean").write_text(
            f"namespace SmallClassNumbers\ntheorem dead_{sc_name} : 1 = 1 := rfl\nend SmallClassNumbers\n",
            encoding="utf-8",
        )

    db_path = tmp_path / "alpo_spine.db"
    ingest_source(spine_proj, db_path)
    run_analysis(db_path)

    out_mat = tmp_path / "alpo_spine_pruned"
    rep = materialize_project(
        db_path,
        source=spine_proj,
        output_dir=out_mat,
        mode="instance-aware",
        strip_dead_decls=True,
        rewrite_imports=True,
    )

    # All 4 dead SmallClassNumbers modules + redundant outer barrel MainTheoremsAll must be dropped!
    assert rep.dropped_modules >= 4
    for sc_name in ("CorGKOf", "ClassNumberThree", "LenEqZeroIff", "OnePoint"):
        assert not (
            out_mat / "src" / "Development" / "AutomorphicArithmetic" / "AutomorphicVarieties" / "SmallClassNumbers" / f"{sc_name}.lean"
        ).exists()

    # And dead_zeta_iff in ClaimStrip must be stripped!
    assert "dead_zeta_iff" not in (
        out_mat / "src" / "Development" / "AutomorphicArithmetic" / "CharacterBoxes" / "ClaimStrip.lean"
    ).read_text(encoding="utf-8")

    orig_loc = count_files_effective_loc(list((spine_proj / "src").rglob("*.lean")))
    pruned_loc = count_files_effective_loc(list((out_mat / "src").rglob("*.lean")))

    # Verify with real `lake build Main` + `#print axioms` on all 5 root theorems in verbatim `Main.lean`!
    gate = verify_refactor_gate(
        out_mat,
        target_modules=["Main"],
        exported_decls=[
            "riemannHypothesis",
            "riemannZeta_eq_zero_re",
            "LFunction_ne_zero_of_half_lt_re",
            "LFunction_eq_zero_re",
            "LFunction_eq_zero_re_of_isPrimitive",
        ],
        before_loc=orig_loc,
        after_loc=pruned_loc,
        run_lake=True,
        lake_bin=lake_bin,
    )
    assert gate.passed is True, f"Verbatim Main.lean spine failed verification gate: {gate.errors}"
    for root_thm in (
        "riemannHypothesis",
        "riemannZeta_eq_zero_re",
        "LFunction_ne_zero_of_half_lt_re",
        "LFunction_eq_zero_re",
        "LFunction_eq_zero_re_of_isPrimitive",
    ):
        axs = set(gate.axiom_check["axioms"].get(root_thm, []))
        assert axs.issubset({"propext", "Classical.choice", "Quot.sound"})
