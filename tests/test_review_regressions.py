"""Regression tests for bugs found in the 2026-11 code review pass."""

from __future__ import annotations

import random
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
    assert set(decls) == {"a", "instFoo", "b", "c", "K"}
    assert decls["a"].end_line == 1
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
