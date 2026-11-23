"""Regression tests for bugs found in the 2026-11 code review pass."""

from __future__ import annotations

import random
import re
from array import array

from proof_compressor.analyze.consolidate import parse_binder_list
from proof_compressor.analyze.dedup import normalize_signature
from proof_compressor.analyze.materialize import strip_lean_comments
from proof_compressor.analyze.merge_modules import _extract_imports_and_body
from proof_compressor.analyze.topology import build_csr, compute_dominators_chk
from proof_compressor.expose.symbols import escape_latex_text
from proof_compressor.ingest.lean_parser import canonical_type_hash, parse_lean_source
from proof_compressor.ingest.stream_archive import TransitiveImportIndex
from proof_compressor.refactor.gate import (
    parse_check_signatures,
    parse_print_axioms,
    verify_refactor_gate,
)


def _decl_names(src: str) -> list[str]:
    return [d.name for d in parse_lean_source(src, "T.M").declarations]


def test_block_comment_containing_line_comment_or_quote_still_closes() -> None:
    assert _decl_names("/- a -- b -/\ntheorem foo : True := trivial\n") == ["foo"]
    assert _decl_names('/- 5" screen -/\ntheorem foo : True := trivial\n') == ["foo"]
    assert _decl_names("/-- doc ---/\ntheorem foo : True := trivial\n") == ["foo"]


def test_parser_declaration_forms() -> None:
    src = (
        "protected nonrec theorem a : True := trivial\n"
        "alias a' := a\n"
        "instance (priority := 100) instFoo : Inhabited Nat := ⟨0⟩\n"
        "/-- doc -/ theorem b : True := trivial\n"
        "@[simp,\n  norm_cast] theorem c : True := trivial\n"
        "class inductive K | x\n"
    )
    decls = {d.name: d for d in parse_lean_source(src, "T.M").declarations}
    assert set(decls) == {"a", "a'", "instFoo", "b", "c", "K"}
    assert decls["a"].end_line == 1
    # `alias` is a declaration: references to it must reach (and keep) its target
    assert decls["a'"].kind == "alias"
    (_, al) = parse_lean_source("theorem card_clean : True := trivial\nalias card' := card_clean\n", "T.M").declarations
    assert al.name == "card'" and al.proof_refs == ["card_clean"]
    assert decls["b"].docstring == "doc"
    assert decls["c"].docstring is None
    assert decls["K"].kind == "class"


def test_open_in_does_not_leak_past_example() -> None:
    src = "open Real in\nexample : True := trivial\ntheorem foo : True := trivial\n"
    (foo,) = parse_lean_source(src, "T.M").declarations
    assert foo.open_namespaces == ()


def test_type_ascription_is_not_a_binder() -> None:
    assert canonical_type_hash("(x : ℝ) : ((cos x : ℂ)) = 1") != canonical_type_hash(
        "(x : ℝ) : ((sin x : ℂ)) = 1"
    )
    assert canonical_type_hash("(a b : ℕ) (h : a < b) : a ≤ b") == canonical_type_hash(
        "(c d : ℕ) (k : c < d) : c ≤ d"
    )


def test_normalize_signature_keeps_projection_binders() -> None:
    a = normalize_signature("(s t : ℂ) (h : s.re < t.re) : f s = 0")
    b = normalize_signature("(s t : ℂ) (h : t.re < s.re) : f s = 0")
    assert a != b


def test_print_axioms_and_check_parse_primes_unicode_and_wrapping() -> None:
    ax = parse_print_axioms(
        "'Foo.mul_le'_of_pos' depends on axioms: [propext]\n'Demo.C2'' does not depend on any axioms\n"
    )
    assert ax == {"Foo.mul_le'_of_pos": ["propext"], "Demo.C2'": []}
    sigs = parse_check_signatures("@Foo.h₁_pos : ∀ {a b : ℕ},\n  a ≤ b → a ≤ b\nFoo.x : Nat\n")
    assert sigs == {"Foo.h₁_pos": "∀ {a b : ℕ}, a ≤ b → a ≤ b", "Foo.x": "Nat"}


def test_gate_build_only_mode_and_baseline_axiom_invariance(tmp_path) -> None:
    def runner(cmd, cwd, env, timeout_s):
        if "build" in cmd:
            return 0, "", ""
        return 0, "'A.t' depends on axioms: [propext, Classical.choice]\n", ""

    build_only = verify_refactor_gate(tmp_path, run_lake=True, check_loc=False, command_runner=runner)
    assert build_only.passed

    grew = verify_refactor_gate(
        tmp_path,
        exported_decls=["A.t"],
        baseline_axioms={"A.t": ["propext"]},
        before_loc=2,
        after_loc=1,
        command_runner=runner,
    )
    assert not grew.passed
    assert grew.axiom_check["disallowed_axioms"] == {"A.t": ["Classical.choice"]}


def test_escape_latex_text_backslash_single_pass() -> None:
    assert escape_latex_text(r"\zeta {x}") == r"\textbackslash{}zeta \{x\}"


def test_strip_lean_comments_preserves_strings_and_library_notes() -> None:
    src = 'def a := r"C:\\" -- c\ndef m := "a\n\n\nb"\nlibrary_note "n"/-- text -/\n'
    out, _ = strip_lean_comments(src)
    assert 'r"C:\\"' in out and "-- c" not in out
    assert '"a\n\n\nb"' in out
    assert 'library_note "n"/-- text -/' in out


def test_merge_header_imports_after_leading_comment() -> None:
    imports, body = _extract_imports_and_body(
        "/-\nCopyright\n-/\nimport Mathlib.A\n-- x\nimport Proj.B\n\ntheorem t : True := trivial\n"
    )
    assert imports == ["Mathlib.A", "Proj.B"]
    assert body[-1].startswith("theorem t")


def test_parse_binder_list_multiline_variable_joined() -> None:
    assert [b.var_name for b in parse_binder_list("{R : Type} (r : R)") or []] == ["R", "r"]


def test_dominators_seed_unreachable_cycle_from_source_component() -> None:
    # C=0, A=1, B=2; A <-> B cycle with A -> C and no roots.
    o, ot, i, it = build_csr(3, [(1, 2), (2, 1), (1, 0)])
    idom, _depth, count, _loc = compute_dominators_chk(3, [], o, ot, i, it, array("Q", [1, 1, 1]))
    assert idom[0] == 1
    assert count[1] == 3


def test_transitive_import_closure_survives_lru_eviction() -> None:
    for seed in range(25):
        rnd = random.Random(seed)
        n = 60
        direct = {i: rnd.sample(range(1, i), min(i - 1, rnd.randint(0, 3))) for i in range(2, n + 1)}
        idx = TransitiveImportIndex(n, direct, max_pinned_hubs=0, max_lru_entries=3)
        order = list(range(1, n + 1))
        rnd.shuffle(order)
        for m in order:
            seen, stack = {m}, [m]
            while stack:
                for v in direct.get(stack.pop(), ()):
                    if v not in seen:
                        seen.add(v)
                        stack.append(v)
            expected = 0
            for v in seen:
                expected |= 1 << idx.topo_bit[v]
            assert idx._get_int_bitset(m) == expected


def test_unicode_and_proof_local_names_are_not_references() -> None:
    src = (
        "theorem t (σ : ℕ) (hσ : 0 < σ) : True := by\n"
        "  intro hτ\n"
        "  obtain ⟨B, hB⟩ := foo\n"
        "  exact bar hσ hτ hB (Baz.primφ σ) range_comp_ι_subset\n"
    )
    (d,) = parse_lean_source(src, "T.M").declarations
    assert d.proof_refs == ["foo", "bar", "Baz.primφ", "range_comp_ι_subset"]


def test_merge_keeps_namespace_that_would_hijack_open_in_separate_file() -> None:
    from proof_compressor.analyze.merge_modules import merge_project_modules

    mods = {
        "RT.TS.Real": ("src/RT/TS/Real.lean", "import Mathlib\nnamespace RT.TS.Real\ntheorem c : True := trivial\nend RT.TS.Real\n"),
        "RT.TS.Est": ("src/RT/TS/Est.lean", "import Mathlib\nnamespace RT.TS.Est\nopen Real\ntheorem e : True := trivial\nend RT.TS.Est\n"),
        "RT.TS.Other": ("src/RT/TS/Other.lean", "import Mathlib\nnamespace RT.TS.Other\ntheorem o : True := trivial\nend RT.TS.Other\n"),
    }
    files, _ = merge_project_modules(mods, target_module_loc=1000, consolidate_duplicates=False)
    real_file = next(t for _, t in files.values() if "namespace RT.TS.Real" in t)
    assert "open Real" not in real_file


def test_greek_and_bang_declaration_names_are_not_anonymous() -> None:
    src = (
        "namespace G\n"
        "theorem δ_comp_map : True := trivial\n"
        "theorem Foo.ιMulti_ne : True := trivial\n"
        "def get! : Nat := 0\n"
        "end G\n"
    )
    assert _decl_names(src) == ["G.δ_comp_map", "G.Foo.ιMulti_ne", "G.get!"]


def test_materialize_fixes_open_hijack_dropped_open_examples_and_generated_refs(tmp_path) -> None:
    from proof_compressor.analyze import run_analysis
    from proof_compressor.analyze.materialize import materialize_project
    from proof_compressor.ingest.stream_archive import ingest_source

    proj = tmp_path / "proj"
    src = proj / "src"
    src.mkdir(parents=True)
    (proj / "lakefile.toml").write_text('name = "t"\nsrcDir = "src"\n', encoding="utf-8")
    files = {
        "Defs": (
            "namespace P\n"
            "theorem δ_comp : 1 = 1 := rfl\n"
            "theorem base_comp : 2 = 2 := rfl\n"
            "theorem only_in_example : 3 = 3 := rfl\n"
            "end P\n"
        ),
        # Entirely dead: its namespace `P.ComplexAt` disappears from the output.
        "Ns": (
            "namespace P\n"
            "def ComplexAt (n : Nat) : Type := Fin n\n"
            "namespace ComplexAt\ntheorem helper : 4 = 4 := rfl\nend ComplexAt\n"
            "end P\n"
        ),
        # Dead and unimported, but declares `P.Complex`, which could hijack `open Complex`.
        "Other": "namespace P.Complex\ntheorem shadow : 5 = 5 := rfl\nend P.Complex\n",
        "Lemmas": (
            "import Ns\n"
            "namespace P\n"
            "open ComplexAt\n"
            "theorem lem_kept : 6 = 6 := rfl\n"
            "theorem lem_dead : 4 = 4 := helper\n"
            "end P\n"
        ),
        "Main": (
            "import Defs\nimport Lemmas\n"
            "namespace P\n"
            "open Complex\n"
            "theorem root : 1 = 1 ∧ 6 = 6 := by\n"
            "  have h := base_comp_assoc\n"
            "  exact ⟨δ_comp, lem_kept⟩\n"
            "example : 3 = 3 := only_in_example\n"
            "end P\n"
        ),
    }
    for name, text in files.items():
        (src / f"{name}.lean").write_text(text, encoding="utf-8")

    db = tmp_path / "t.db"
    ingest_source(proj, db)
    run_analysis(db, roots=["P.root"])
    out = tmp_path / "out"
    materialize_project(
        db, source=proj, output_dir=out, roots=["P.root"], mode="instance-aware", strip_dead_decls=True
    )

    main = (out / "src" / "Main.lean").read_text(encoding="utf-8")
    assert "open _root_.Complex" in main
    assert "example" not in main
    lemmas = (out / "src" / "Lemmas.lean").read_text(encoding="utf-8")
    assert "open ComplexAt" not in lemmas and "lem_dead" not in lemmas
    defs = (out / "src" / "Defs.lean").read_text(encoding="utf-8")
    assert "δ_comp" in defs and "base_comp" in defs and "only_in_example" not in defs


def test_materialize_drops_open_of_namespace_declared_only_later_in_file(tmp_path) -> None:
    from proof_compressor.analyze import run_analysis
    from proof_compressor.analyze.materialize import materialize_project
    from proof_compressor.ingest.stream_archive import ingest_source

    proj = tmp_path / "proj"
    (proj / "src").mkdir(parents=True)
    (proj / "lakefile.toml").write_text('name = "t"\nsrcDir = "src"\n', encoding="utf-8")
    (proj / "src" / "Shift.lean").write_text(
        "namespace G.Et.Triv\ndef shift : Nat := 0\nend G.Et.Triv\n", encoding="utf-8"
    )
    (proj / "src" / "Main.lean").write_text(
        "import Shift\nopen G.Et.Triv\nopen G.Et.Triv (shift)\nnamespace G.Et.Triv\ntheorem root : 1 = 1 := rfl\nend G.Et.Triv\n",
        encoding="utf-8",
    )
    db = tmp_path / "t.db"
    ingest_source(proj, db)
    run_analysis(db, roots=["G.Et.Triv.root"])
    out = tmp_path / "out"
    materialize_project(
        db, source=proj, output_dir=out, roots=["G.Et.Triv.root"], mode="instance-aware", strip_dead_decls=True
    )
    main = (out / "src" / "Main.lean").read_text(encoding="utf-8")
    assert "import Shift" not in main
    assert "open G.Et.Triv" not in main


def test_open_resolution_ignores_namespaces_declared_later_and_unknown_roots(tmp_path) -> None:
    from proof_compressor.analyze import run_analysis
    from proof_compressor.analyze.materialize import materialize_project
    from proof_compressor.ingest.stream_archive import ingest_source

    proj = tmp_path / "proj"
    (proj / "src").mkdir(parents=True)
    (proj / "lakefile.toml").write_text('name = "t"\nsrcDir = "src"\n', encoding="utf-8")
    # `P.Limits` exists somewhere, so `open Limits` inside `namespace P` is shadowable, but `Limits`
    # may resolve relative to the opened `CategoryTheory`: it must not become `_root_.Limits`.
    (proj / "src" / "Other.lean").write_text("namespace P.Limits\ntheorem z : 0 = 0 := rfl\nend P.Limits\n", encoding="utf-8")
    (proj / "src" / "Main.lean").write_text(
        "namespace P\n"
        "open CategoryTheory Limits\n"
        "open scoped RestrictedProduct\n"
        "namespace RestrictedProduct\n"
        "theorem root : 1 = 1 := rfl\n"
        "end RestrictedProduct\n"
        "end P\n",
        encoding="utf-8",
    )
    db = tmp_path / "t.db"
    ingest_source(proj, db)
    run_analysis(db, roots=["P.RestrictedProduct.root"])
    out = tmp_path / "out"
    materialize_project(
        db, source=proj, output_dir=out, roots=["P.RestrictedProduct.root"], mode="instance-aware", strip_dead_decls=True
    )
    main = (out / "src" / "Main.lean").read_text(encoding="utf-8")
    assert "open CategoryTheory Limits" in main
    assert "open scoped RestrictedProduct" in main


def _merge(mods: dict[str, str], **kw):
    from proof_compressor.analyze.merge_modules import merge_project_modules

    srcs = {m: (f"src/{m.replace('.', '/')}.lean", t) for m, t in mods.items()}
    return merge_project_modules(srcs, target_module_loc=1000, consolidate_duplicates=False, **kw)


def test_merge_keeps_capturing_declaration_out_of_the_same_file() -> None:
    # `P.Util.contDiff_exp` would capture the Mathlib `contDiff_exp` that `P.Use.t` means.
    files, rep = _merge(
        {
            "P.Util": "import Mathlib\nnamespace P\ntheorem contDiff_exp : True := trivial\nend P\n",
            "P.Use": "import Mathlib\nnamespace P\ntheorem t : True := by\n  have := contDiff_exp.comp foo\n  trivial\nend P\n",
            "P.Other": "import Mathlib\nnamespace P\ntheorem o : True := trivial\nend P\n",
        }
    )
    assert rep.capture_hazard_names == 1
    use_file = next(t for _, t in files.values() if "theorem t " in t)
    assert "theorem contDiff_exp" not in use_file
    assert "theorem o " in use_file


def test_merge_allows_reference_to_imported_same_namespace_declaration() -> None:
    files, rep = _merge(
        {
            "P.Util": "import Mathlib\nnamespace P\ntheorem helper : True := trivial\nend P\n",
            "P.Use": "import P.Util\nnamespace P\ntheorem t : True := helper\nend P\n",
        }
    )
    assert rep.capture_hazard_names == 0
    assert len(files) == 1


def test_merge_separates_partial_mathlib_environment() -> None:
    files, rep = _merge(
        {
            "P.A": "import Mathlib.Data.Nat.Basic\nnamespace P.A\ntheorem a : True := trivial\nend P.A\n",
            "P.B": "import Mathlib\nnamespace P.B\ntheorem b : True := trivial\nend P.B\n",
            "P.C": "import Mathlib\nimport Mathlib.Data.Nat.Basic\nnamespace P.C\ntheorem c : True := trivial\nend P.C\n",
        }
    )
    assert rep.partial_env_modules == 1
    a_file = next(t for _, t in files.values() if "theorem a " in t)
    assert "theorem b " not in a_file and "import Mathlib\n" not in a_file
    b_file = next(t for _, t in files.values() if "theorem b " in t)
    assert "theorem c " in b_file


def test_variable_types_and_field_notation_become_references() -> None:
    src = (
        "namespace G\n"
        "variable {R : Basic.Ranks} (H : Basic.Host R)\n"
        "  [Foo.Bar R]\n"
        "theorem uses (D : RayData Nat) : H.condN = 1 := by\n"
        "  have := D.clsHom_surjective\n"
        "  exact (mkThing 3).robba\n"
        "end G\n"
        "theorem after : True := trivial\n"
    )
    uses, after = parse_lean_source(src, "T.M").declarations
    assert {"Basic.Ranks", "Basic.Host", "Foo.Bar", "RayData"} <= set(uses.type_refs)
    assert "H.condN" not in uses.type_refs and "D.clsHom_surjective" not in uses.proof_refs
    assert uses.type_field_refs == ["Host|condN"]
    assert uses.proof_field_refs == ["RayData|clsHom_surjective", "|robba"]
    assert after.type_refs == ["True"]


def test_field_notation_keeps_target_and_dead_variable_line_is_stripped(tmp_path) -> None:
    from proof_compressor.analyze import run_analysis
    from proof_compressor.analyze.materialize import materialize_project
    from proof_compressor.ingest.stream_archive import ingest_source

    proj = tmp_path / "proj"
    (proj / "src").mkdir(parents=True)
    (proj / "lakefile.toml").write_text('name = "t"\nsrcDir = "src"\n', encoding="utf-8")
    (proj / "src" / "Dead.lean").write_text("structure DeadTy where\n  x : Nat\n", encoding="utf-8")
    (proj / "src" / "Main.lean").write_text(
        "import Dead\n"
        "namespace G\n"
        "structure RayData where\n  x : Nat\n"
        "theorem RayData.surj (D : RayData) : D.x = D.x := rfl\n"
        "theorem RayData.unused (D : RayData) : D.x = D.x := rfl\n"
        "theorem root (D : RayData) : D.x = D.x := D.surj\n"
        "section Tail\n"
        "variable (Z : DeadTy)\n"
        "theorem dead_tail : Z.x = Z.x := rfl\n"
        "end Tail\n"
        "end G\n",
        encoding="utf-8",
    )
    db = tmp_path / "t.db"
    ingest_source(proj, db)
    run_analysis(db, roots=["G.root"])
    out = tmp_path / "out"
    materialize_project(db, source=proj, output_dir=out, roots=["G.root"], mode="instance-aware", strip_dead_decls=True)
    main = (out / "src" / "Main.lean").read_text(encoding="utf-8")
    assert "theorem RayData.surj" in main and "RayData.unused" not in main
    assert "dead_tail" not in main and "variable (Z : DeadTy)" not in main
    assert "import Dead" not in main


def test_external_namespace_list_pins_shadowable_open(tmp_path) -> None:
    from proof_compressor.analyze import run_analysis
    from proof_compressor.analyze.materialize import materialize_project
    from proof_compressor.ingest.stream_archive import ingest_source

    proj = tmp_path / "proj"
    (proj / "src").mkdir(parents=True)
    (proj / "lakefile.toml").write_text('name = "t"\nsrcDir = "src"\n', encoding="utf-8")
    (proj / "src" / "Other.lean").write_text(
        "namespace P.RestrictedProduct\ntheorem z : 0 = 0 := rfl\nend P.RestrictedProduct\n"
        "namespace P.Limits\ntheorem y : 0 = 0 := rfl\nend P.Limits\n",
        encoding="utf-8",
    )
    (proj / "src" / "Main.lean").write_text(
        "namespace P\nopen CategoryTheory Limits\nopen scoped RestrictedProduct\ntheorem root : 1 = 1 := rfl\nend P\n",
        encoding="utf-8",
    )
    db = tmp_path / "t.db"
    ingest_source(proj, db)
    run_analysis(db, roots=["P.root"])
    out = tmp_path / "out"
    materialize_project(
        db, source=proj, output_dir=out, roots=["P.root"], mode="instance-aware",
        external_namespaces=["RestrictedProduct", "CategoryTheory", "CategoryTheory.Limits"],
    )
    main = (out / "src" / "Main.lean").read_text(encoding="utf-8")
    assert "open scoped _root_.RestrictedProduct" in main
    assert "open CategoryTheory Limits" in main


_CAPTURE_MODS = {
    # `P.M` declares `P.contDiff_exp`; `P.U` never imports it but ends up seeing it, because
    # its bundle-mates `P.V`/`P.W` do.
    "P.M": "import Mathlib\nnamespace P\ntheorem contDiff_exp : True := trivial\nend P\n",
    "P.D": "import Mathlib\nnamespace P.D\ntheorem d : True := trivial\nend P.D\n",
    "P.U": (
        "import P.D\nnamespace P\nopen Real\n"
        "theorem t : True := by\n  have := contDiff_exp.comp foo\n  trivial\n"
        "theorem t2 (contDiff_exp : Nat) : contDiff_exp = contDiff_exp := rfl\n"
        "theorem t3 : True := by\n  have := local_thing\n  trivial\n"
        "structure S where\n  contDiff : Nat\n  ok : contDiff_exp = contDiff_exp\n"
        "section\nvariable (h : contDiff_exp = contDiff_exp)\n"
        "theorem t4 : True := by\n  have := h\n  trivial\nend\n"
        "end P\n"
    ),
    "P.V": "import P.D\nimport P.M\nnamespace P.V\ntheorem v : True := P.contDiff_exp\nend P.V\n",
    "P.W": "import P.M\nnamespace P.W\ntheorem local_thing : True := trivial\ntheorem w : True := P.contDiff_exp\nend P.W\n",
}


def test_merge_qualifies_reference_captured_through_a_bundle_import() -> None:
    files, rep = _merge(_CAPTURE_MODS, external_names=frozenset({"Real.contDiff_exp", "True", "Nat"}))
    u_file = next(t for _, t in files.values() if "theorem t " in t)
    assert "theorem contDiff_exp" not in u_file
    assert "have := _root_.Real.contDiff_exp.comp foo" in u_file
    # the binder of the same name and the declaration in `P.M` stay as written
    assert "theorem t2 (contDiff_exp : Nat) : contDiff_exp = contDiff_exp" in u_file
    m_file = next(t for _, t in files.values() if "theorem contDiff_exp : True" in t)
    assert "_root_" not in m_file
    assert "  ok : _root_.Real.contDiff_exp = _root_.Real.contDiff_exp" in u_file
    assert "variable (h : _root_.Real.contDiff_exp = _root_.Real.contDiff_exp)" in u_file
    assert rep.capture_fixed_sites == 3 and rep.capture_unfixable_sites == 0


def test_merge_without_external_names_reports_capture_it_cannot_fix() -> None:
    _files, rep = _merge(_CAPTURE_MODS)
    assert rep.capture_fixed_sites == 0
    assert rep.capture_unfixable_sites >= 1 and rep.cross_bundle_capture_examples


def test_merge_protects_declaration_that_would_capture_an_overloaded_name() -> None:
    mods = {
        "A.M1": "import Mathlib\nnamespace A\ndef rr (n : Nat) : Nat := n\nend A\n",
        "B.M2": "import Mathlib\nnamespace B\ndef rr (s : String) : String := s\nend B\n",
        "P.M": (
            "import Mathlib\nnamespace P\n"
            "noncomputable def rr (b : Bool) : Bool := b\n"
            "theorem uses_r : rr true = true := rfl\n"
            "theorem uses_r' : rr.foo = (rr) := rfl\n"
            "end P\n"
        ),
        "P.D": "import Mathlib\nnamespace P.D\ntheorem d : True := trivial\nend P.D\n",
        "P.U": (
            "import P.D\nimport A.M1\nimport B.M2\nnamespace P\nopen A B\n"
            "theorem t : rr 3 = 3 := rfl\ndef muF : Thing := mk\nend P\n"
        ),
        "P.V": "import P.D\nimport P.M\nnamespace P.V\ntheorem v : P.rr true = true := rfl\nend P.V\n",
        "P.W": "import P.M\nnamespace P.W\nopen P\ntheorem w : rr true = true := rfl\nend P.W\n",
    }
    files, rep = _merge(mods, external_names=frozenset({"Nat", "String", "Bool", "True", "rfl"}))
    text = "\n".join(t for _, t in files.values())
    assert "protected noncomputable def rr (b : Bool) : Bool := b" in text
    assert "theorem uses_r : _root_.P.rr true = true := rfl" in text
    assert "theorem uses_r' : _root_.P.rr.foo = (_root_.P.rr) := rfl" in text
    assert "theorem w : _root_.P.rr true = true := rfl" in text
    assert "theorem v : P.rr true = true := rfl" in text  # already qualified
    assert "theorem t : rr 3 = 3 := rfl" in text  # the overloaded site keeps its overload
    assert rep.capture_protected_decls == 1 and rep.capture_protected_ref_sites == 4
    assert rep.capture_unfixable_sites == 0


def test_qualify_token_leaves_fields_and_named_arguments() -> None:
    from proof_compressor.analyze.merge_modules import _qualify_token

    src = "def muF (n : ℕ) : Fld := mk (Fld := 3) Fld\n  Fld := 1\n  x ∈ Fld := by simp [Fld.a, a.Fld]\n"
    out, k = _qualify_token(src, "Fld", "_root_.N.Fld")
    assert out == (
        "def muF (n : ℕ) : _root_.N.Fld := mk (Fld := 3) _root_.N.Fld\n  Fld := 1\n"
        "  x ∈ _root_.N.Fld := by simp [Fld.a, a.Fld]\n"
    )
    assert k == 3


def test_lean_type_to_latex_drops_root_prefix_and_dangling_script_operator() -> None:
    from proof_compressor.expose.symbols import lean_type_to_latex

    out = lean_type_to_latex(": ∀ (h : _root_.Foo.RecTExists) (z : ℂ), z ^ 2 = 1", max_len=44)
    assert "_root" not in out
    assert not re.search(r"\^\s*(\\[;,]|$)", out)
