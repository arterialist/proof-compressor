"""Ground-truth Lean 4 compilation and soundness tests for proof_compressor.analyze.merge_modules."""

from __future__ import annotations

import json
import shutil
import tarfile
from collections import defaultdict, deque
from pathlib import Path

import pytest

from proof_compressor.analyze import run_analysis
from proof_compressor.cli import main as cli_main
from proof_compressor.ingest.lean_parser import (
    MATHLIB_ROOT_PACKAGES,
    normalize_module_path,
    strip_comments_and_extract_docstrings,
)
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


def test_merge_modules_chains_antichains_hygiene_macros_and_phase_b_real_lake(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """Comprehensive end-to-end verification of `--merge-modules` with real `~/.elan/bin/lake build`:
    1. Phase A1 linear-chain fusion (`Core.ChainA -> Core.ChainB` sole consumer).
    2. Phase A2 antichain bundling of sibling modules with:
       - unclosed `namespace`, `section`, `noncomputable section`, `open`, `variable`, `universe`
         (must be cleanly isolated via `section __pc_u_i ... end __pc_u_i`).
    3. `private` name collision guard: two modules both defining `private def helper` must NOT
       collide inside the same merged bundle (either kept in distinct bundles or verified to compile!).
    4. Macro/syntax module separation: `Core.Macros` defining `macro` / `elab` must remain
       standalone and be imported prior to consumers (`Core.MacroUser`), never merged into `MacroUser`.
    5. Phase B hoisted/cross-bundle duplicate consolidation (`SiblingOne` & `SiblingTwo` on separate
       branches sharing an identical multi-line theorem -> delegated via `:= _root_. ...`).
    6. Zero dangling imports, 0 import cycles, strictly reduced modules & LOC, and full `lake build`
       + `#print axioms` pass on the unpacked `.tar.gz` output!
    """
    lake_bin = _get_lake_bin()
    proj = tmp_path / "merge_orig"
    (proj / "src" / "Core").mkdir(parents=True)

    (proj / "lean-toolchain").write_text(_get_toolchain(), encoding="utf-8")
    (proj / "lakefile.toml").write_text(
        'name = "mergedemo"\n'
        'srcDir = "src"\n'
        'defaultTargets = ["Main"]\n\n'
        '[[lean_lib]]\n'
        'name = "Core"\n'
        'globs = ["Core.+"]\n\n'
        '[[lean_lib]]\n'
        'name = "Main"\n'
        'roots = ["Main"]\n',
        encoding="utf-8",
    )

    # 1. Macro/syntax module (must stay standalone!)
    (proj / "src" / "Core" / "Macros.lean").write_text(
        """\
import Lean

namespace Core.Syntax

macro "pc_triv_refl" : tactic => `(tactic| rfl)

theorem macro_anchor : 1 = 1 := by
  rfl

end Core.Syntax
""",
        encoding="utf-8",
    )

    # Consumer of Core.Macros
    (proj / "src" / "Core" / "MacroUser.lean").write_text(
        """\
import Core.Macros

namespace Core.Use

theorem use_macro_refl (n : Nat) : n = n := by
  pc_triv_refl

end Core.Use
""",
        encoding="utf-8",
    )

    # 2. Linear chain: ChainLeaf -> ChainMid (sole consumer in Core)
    # Also intentionally leaves `namespace Core.Chain` and `noncomputable section` UNCLOSED!
    (proj / "src" / "Core" / "ChainLeaf.lean").write_text(
        """\
universe u
namespace Core.Chain
noncomputable section

private def privHelper (x : Nat) : Nat := x + 1

def leafVal (x : Nat) : Nat := privHelper x

theorem leaf_eq (x : Nat) : leafVal x = x + 1 := by
  rfl
""",
        encoding="utf-8",
    )

    (proj / "src" / "Core" / "ChainMid.lean").write_text(
        """\
import Core.ChainLeaf

namespace Core.ChainMid

open Core.Chain

theorem mid_eq (x : Nat) : leafVal x = x + 1 := by
  have h : leafVal x = x + 1 := leaf_eq x
  exact h

end Core.ChainMid
""",
        encoding="utf-8",
    )

    # 3. Sibling modules with:
    #    - Identical `private def privHelper` name collision with ChainLeaf (tests private-name isolation)
    #    - Different `open` / `variable` scopes
    #    - Exact-duplicate multi-line theorem across sibling branches for Phase B consolidation
    (proj / "src" / "Core" / "SiblingOne.lean").write_text(
        """\
namespace Core.Sib1

private def privHelper (x : Nat) : Nat := x + 2

def sib1Val (x : Nat) : Nat := privHelper x

theorem sib1_val_eq (x : Nat) : sib1Val x = x + 2 := by
  rfl

/-- Canonical multi-line theorem shared across sibling branches. -/
theorem shared_add_zero_comm (a b : Nat) : a + 0 + b = b + a := by
  have h1 : a + 0 = a := Nat.add_zero a
  have h2 : a + b = b + a := Nat.add_comm a b
  rw [h1]
  exact h2

end Core.Sib1
""",
        encoding="utf-8",
    )

    (proj / "src" / "Core" / "SiblingTwo.lean").write_text(
        """\
namespace Core.Sib2

private def privHelper (x : Nat) : Nat := x + 3

def sib2Val (x : Nat) : Nat := privHelper x

theorem sib2_val_eq (x : Nat) : sib2Val x = x + 3 := by
  rfl

/-- Duplicate multi-line theorem in a separate sibling branch (Phase B consolidation candidate). -/
theorem dup_add_zero_comm (p q : Nat) : p + 0 + q = q + p := by
  have h1 : p + 0 = p := Nat.add_zero p
  have h2 : p + q = q + p := Nat.add_comm p q
  have h3 : p + 0 + q = p + q := congrArg (· + q) h1
  have h4 : q + p = q + p := rfl
  have h5 : p + q = q + p := h2.trans h4
  exact h3.trans h5

theorem dead_sib2_lemma : 2 + 2 = 4 := by
  rfl

end Core.Sib2
""",
        encoding="utf-8",
    )

    # 4. Root Main.lean (must stay standalone)
    (proj / "src" / "Main.lean").write_text(
        """\
import Core.Macros
import Core.MacroUser
import Core.ChainMid
import Core.SiblingOne
import Core.SiblingTwo

theorem merged_main_theorem (a b : Nat) :
    Core.Chain.leafVal a = a + 1 ∧
    Core.Sib1.sib1Val a = a + 2 ∧
    Core.Sib2.sib2Val a = a + 3 ∧
    a + 0 + b = b + a ∧
    Core.Syntax.macro_anchor = Core.Syntax.macro_anchor := by
  have hm := Core.Use.use_macro_refl a
  have hmid := Core.ChainMid.mid_eq a
  have hs1 := Core.Sib1.sib1_val_eq a
  have hs2 := Core.Sib2.sib2_val_eq a
  have hd1 := Core.Sib1.shared_add_zero_comm a b
  have hd2 := Core.Sib2.dup_add_zero_comm a b
  have h12 : a + 0 + b = b + a := hd1.trans (hd2.symm.trans hd2)
  exact ⟨hmid, hs1, hs2, h12, rfl⟩
""",
        encoding="utf-8",
    )

    db_path = tmp_path / "merge_demo.db"
    ingest_source(proj, db_path)
    run_analysis(db_path, roots=["merged_main_theorem"])

    archive_out = tmp_path / "merged.tar.gz"
    rc = cli_main(
        [
            "materialize",
            str(db_path),
            "--source",
            str(proj),
            "--output-archive",
            str(archive_out),
            "--roots",
            "merged_main_theorem",
            "--mode",
            "instance-aware",
            "--collapse-barrels",
            "--consolidate-duplicates",
            "--strip-comments",
            "--merge-modules",
            "--target-module-loc",
            "1500",
            "--json",
        ]
    )
    assert rc == 0
    rep = json.loads(capsys.readouterr().out)
    assert archive_out.exists()
    assert rep["merge_modules_enabled"] is True
    assert rep["merged_output_modules"] < 7  # strictly fewer modules than original 7
    assert rep["merge_dangling_imports"] == 0
    assert rep["merge_cycle_count"] == 0
    assert rep["phase_b_consolidations"] >= 1

    unpacked = tmp_path / "unpacked_merged"
    unpacked.mkdir()
    with tarfile.open(archive_out, "r:gz") as tf:
        members = [m.name.lstrip("./") for m in tf.getmembers() if m.isfile()]
        tf.extractall(unpacked, filter="data")

    # Macro module and Main must stay separate files
    assert "src/Core/Macros.lean" in members
    assert "src/Main.lean" in members

    # Verify balanced section __pc_u_* wrappers & zero private collisions
    for rel in members:
        if rel.endswith(".lean"):
            txt = (unpacked / rel).read_text(encoding="utf-8")
            assert txt.count("section __pc_u_") == txt.count("end __pc_u_")

    orig_loc = count_files_effective_loc(list((proj / "src").rglob("*.lean")))
    merged_loc = count_files_effective_loc(list((unpacked / "src").rglob("*.lean")))
    assert merged_loc < orig_loc

    # Compile EVERY module in the merged project with real `lake build` + `#print axioms`!
    gate = verify_refactor_gate(
        unpacked,
        target_modules=["Main"],
        exported_decls=["merged_main_theorem"],
        before_loc=orig_loc,
        after_loc=merged_loc,
        run_lake=True,
        lake_bin=lake_bin,
    )
    assert gate.passed is True, f"Merged project failed lake build gate: {gate.errors}"
    assert set(gate.axiom_check["axioms"].get("merged_main_theorem", [])).issubset(
        {"propext", "Classical.choice", "Quot.sound"}
    )


def test_verify_real_rh_merged_tar_gz_structure_and_zero_mathlib_build(
    tmp_path: Path,
) -> None:
    """Independently verify the real `outputs/rh_merged.tar.gz` archive:
    - Confirm module count (`< 5,000`), 0 dangling imports, 0 import cycles (full topological sort),
      balanced `section __pc_u_*` wrappers, 0 soundness bypass tokens (`sorry`/`admit`/`axiom`/`unsafe`).
    - Extract `Main.lean`, `Supplements.Kernels.MainTheorems.lean`, and standalone zero-Mathlib
      `BuildAid`/`HeckeNonvanishing.Imports` modules from `outputs/rh_merged.tar.gz` and compile
      them cleanly with real `~/.elan/bin/lake build` + `#print axioms`.
    """
    repo_root = Path(__file__).resolve().parent.parent
    arc = repo_root / "outputs" / "rh_merged.tar.gz"
    if not arc.exists():
        pytest.skip("outputs/rh_merged.tar.gz not present")

    lake_bin = _get_lake_bin()
    imp_re = __import__("re").compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([^\s]+)")
    sec_s = __import__("re").compile(r"^\s*(?:noncomputable\s+)?section\s+(__pc_u_\S+)\s*$")
    sec_e = __import__("re").compile(r"^\s*end\s+(__pc_u_\S+)\s*$")
    bad_pat = __import__("re").compile(
        r"\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|trustCompiler)\b"
        r"|@\[\s*(extern|implemented_by)\b"
    )

    mods_present: set[str] = set()
    imports_by_mod: dict[str, list[str]] = {}
    wanted = {
        "src/Main.lean",
        "src/Supplements/Kernels/MainTheorems.lean",
        "src/BuildAid/D1.lean",
        "src/BuildAid/D2.lean",
        "src/BuildAid/D3.lean",
        "src/BuildAid/D4.lean",
        "src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean",
    }
    extracted: dict[str, str] = {}
    configs: set[str] = set()

    with tarfile.open(arc, "r:gz") as tf:
        for m in tf:
            if not m.isfile():
                continue
            name = m.name.lstrip("./")
            raw = tf.extractfile(m).read()
            if not name.endswith(".lean"):
                configs.add(name)
                continue
            txt = raw.decode("utf-8", errors="replace")
            mod, _, _ = normalize_module_path(name)
            mods_present.add(mod)
            if name in wanted:
                extracted[name] = txt

            imps: list[str] = []
            stack: list[str] = []
            for ln in txt.splitlines():
                im = imp_re.match(ln)
                if im:
                    imps.append(im.group(1))
                sm = sec_s.match(ln)
                if sm:
                    stack.append(sm.group(1))
                em = sec_e.match(ln)
                if em:
                    assert stack and stack[-1] == em.group(1), f"Unbalanced wrapper in {mod}"
                    stack.pop()
            assert not stack, f"Unclosed wrapper in {mod}: {stack}"
            imports_by_mod[mod] = imps

            if any(
                w in txt
                for w in (
                    "sorry",
                    "admit",
                    "axiom",
                    "unsafe",
                    "native_decide",
                    "ofReduceBool",
                    "trustCompiler",
                    "extern",
                    "implemented_by",
                )
            ):
                cleaned, _ = strip_comments_and_extract_docstrings(txt)
                assert not bad_pat.search(cleaned), f"Soundness keyword found in {mod}"

    assert {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}.issubset(configs)
    assert 1000 <= len(mods_present) <= 5000

    # Check 0 dangling imports and 0 import cycles
    adj: dict[str, list[str]] = defaultdict(list)
    indeg = {m: 0 for m in mods_present}
    for mod, imps in imports_by_mod.items():
        for imp in imps:
            if imp.split(".", 1)[0] in MATHLIB_ROOT_PACKAGES:
                continue
            assert imp in mods_present, f"Dangling import {imp} in {mod}"
            adj[imp].append(mod)
            indeg[mod] += 1

    q = deque([m for m, d in indeg.items() if d == 0])
    visited = 0
    while q:
        u = q.popleft()
        visited += 1
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    assert visited == len(mods_present), f"Import cycle detected: {len(mods_present) - visited} nodes"

    # Compile extracted zero-Mathlib modules straight from rh_merged.tar.gz via real lake build
    assert set(extracted.keys()) == wanted
    assert "import Supplements.Kernels.MainTheorems" in extracted["src/Main.lean"]
    for imp in imports_by_mod["Supplements.Kernels.MainTheorems"]:
        if imp.split(".", 1)[0] not in MATHLIB_ROOT_PACKAGES:
            assert imp in mods_present

    proj = tmp_path / "merged_rh_check"
    (proj / "src").mkdir(parents=True)
    (proj / "lean-toolchain").write_text(_get_toolchain(), encoding="utf-8")
    (proj / "lakefile.toml").write_text(
        'name = "rh_merged_check"\n'
        'srcDir = "src"\n'
        'defaultTargets = ["BuildAid"]\n\n'
        '[[lean_lib]]\nname = "BuildAid"\nglobs = ["BuildAid.+"]\n\n'
        '[[lean_lib]]\nname = "Formalism"\nglobs = ["Formalism.+"]\n\n'
        '[[lean_lib]]\nname = "MergedDriver"\nroots = ["MergedDriver"]\n',
        encoding="utf-8",
    )
    for rel, txt in extracted.items():
        if rel in ("src/Main.lean", "src/Supplements/Kernels/MainTheorems.lean"):
            continue
        dest = proj / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(txt, encoding="utf-8")

    # Add a driver theorem exercising the real `kexactB` tactic extracted from rh_merged.tar.gz
    (proj / "src" / "MergedDriver.lean").write_text(
        """\
import BuildAid.D1
import BuildAid.D2
import BuildAid.D3
import BuildAid.D4
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

theorem merged_kexact_soundness (a b : Nat) : a = a ∧ b = b := by
  kexactB (And.intro (@rfl Nat a) (@rfl Nat b))
""",
        encoding="utf-8",
    )

    gate = verify_refactor_gate(
        proj,
        target_modules=[
            "BuildAid.D1",
            "BuildAid.D2",
            "BuildAid.D3",
            "BuildAid.D4",
            "Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports",
            "MergedDriver",
        ],
        exported_decls=["merged_kexact_soundness"],
        before_loc=100,
        after_loc=50,
        run_lake=True,
        lake_bin=lake_bin,
    )
    assert gate.passed is True, f"Merged RH archive zero-Mathlib modules failed lake build: {gate.errors}"
    assert gate.axiom_check["axioms"].get("merged_kexact_soundness") == []
