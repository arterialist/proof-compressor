"""Comprehensive tests for proof_compressor.expose and proof_compressor.refactor."""

from __future__ import annotations

import re
import shutil
from pathlib import Path

import pytest

from proof_compressor.analyze import run_analysis
from proof_compressor.expose import expose_all
from proof_compressor.expose.audit import audit_latex, format_audit_markdown
from proof_compressor.expose.blueprint import generate_blueprint
from proof_compressor.expose.filter import (
    classify_bookkeeping,
    detect_bookkeeping_leaks,
    extract_all_cluster_idioms,
    tag_bookkeeping,
)
from proof_compressor.expose.latex import generate_latex
from proof_compressor.expose.symbols import (
    SymbolRegistry,
    build_symbol_registry,
    lean_type_to_latex,
)
from proof_compressor.refactor.gate import (
    count_effective_loc,
    parse_check_signatures,
    parse_print_axioms,
    verify_refactor_gate,
)
from proof_compressor.refactor.planner import (
    format_refactor_plan_markdown,
    plan_refactors,
)

from conftest import build_synthetic_dag_db


@pytest.fixture
def analyzed_db(tmp_path: Path):
    """Return (db_path, info) for a fully analyzed synthetic proof DAG."""
    db_path = tmp_path / "analyzed.db"
    conn, info = build_synthetic_dag_db(
        db_path, num_pillars=5, leaves_per_pillar=15, dead_nodes=40, include_cycle=True
    )
    run_analysis(conn, roots=[info["root"]], max_chapters=6, max_sections=16)
    conn.close()
    return db_path, info


# ---------------------------------------------------------------------------
# symbols.py tests
# ---------------------------------------------------------------------------


def test_symbol_registry_and_lean_type_translation(analyzed_db) -> None:
    db_path, info = analyzed_db
    reg = build_symbol_registry(db_path, max_symbols=50, reachable_only=True)
    assert len(reg.entries) == len(info["defs"])

    # Macros must be strictly alphabetic TeX commands with no duplicates
    macros = [e.latex_macro for e in reg.entries]
    assert len(macros) == len(set(macros))
    for mac in macros:
        assert re.fullmatch(r"\\[A-Za-z]+", mac), f"Invalid TeX macro: {mac}"

    # Reload from SQLite symbols table
    reloaded = SymbolRegistry.load_from_db(db_path)
    assert len(reloaded.entries) == len(reg.entries)

    # Standard mathematical notation & Greek Unicode spacing (no \muG drift!)
    sig = (
        "[CommRing R] (h : Measurable f) (s : ℂ) (μG νq : ℝ) : "
        "riemannZeta s ≠ 0 → Finset.sum S (fun n => vonMangoldt n) ≥ 0"
    )
    tex = lean_type_to_latex(sig, reg)
    assert r"\zeta" in tex
    assert r"\Lambda" in tex
    assert r"\sum" in tex
    assert r"\mathbb{C}" in tex
    assert r"\mu G" in tex and r"\muG" not in tex
    assert r"\nu q" in tex and r"\nuq" not in tex
    assert "Measurable" not in tex
    assert "CommRing" not in tex
    assert "Finset" not in tex


# ---------------------------------------------------------------------------
# filter.py tests
# ---------------------------------------------------------------------------


def test_bookkeeping_classification_and_idioms(analyzed_db) -> None:
    db_path, _info = analyzed_db

    assert classify_bookkeeping("Foo.instInhabited", "instance", "Inhabited ℕ", 1).is_bookkeeping is True
    assert classify_bookkeeping("Foo.lt_or_gt_aux", "lemma", "∀ a b : ℝ, a < b ∨ b ≤ a", 2).is_bookkeeping is True
    assert classify_bookkeeping("Foo.f_measurable", "lemma", "Measurable f", 3).is_bookkeeping is True
    assert classify_bookkeeping("Foo.coe_add", "lemma", "↑(a + b) = ↑a + ↑b", 2).is_bookkeeping is True
    assert (
        classify_bookkeeping(
            "Formalism.BostSlope.bost_slope_inequality",
            "theorem",
            "∀ E : HermitianBundle, deg E ≤ slope E",
            45,
            "Bost slope inequality for Hermitian vector bundles.",
        ).is_bookkeeping
        is False
    )

    stats = tag_bookkeeping(db_path, update_db=True)
    assert stats["total_evaluated"] > 0
    assert stats["bookkeeping_count"] > 0
    assert stats["mathematical_count"] > 0

    # Proof idioms on our synthetic chapters
    idioms_map = extract_all_cluster_idioms(db_path)
    all_idiom_names = {
        item["idiom"] for items in idioms_map.values() for item in items
    }
    assert "iterated theta lift" in all_idiom_names
    assert "seesaw / Bessel period" in all_idiom_names
    assert "Bost slope inequality" in all_idiom_names
    assert "Iwasawa tower" in all_idiom_names
    assert "Vandiver / cohomology" in all_idiom_names

    # Bookkeeping leak detector catches prose leaks but ignores \leanlink & appendix
    dirty = (
        "Because the reals are totally ordered, we apply Finset.sum and Nat.cast coercion.\n"
        r"\leanlink{Foo.Finset.cast_aux}" "\n"
        r"\appendix" "\n"
        "Appendix mentions Finset.sum and Nat.cast legitimately.\n"
    )
    leaks = detect_bookkeeping_leaks(dirty)
    leak_kinds = {l["kind"] for l in leaks}
    assert "trivial_order_leak" in leak_kinds
    assert "finset_leak" in leak_kinds
    assert "coercion_leak" in leak_kinds
    # None of the leaks should come from lines >= 2
    assert all(l["line"] == 1 for l in leaks)


# ---------------------------------------------------------------------------
# latex.py & blueprint.py tests
# ---------------------------------------------------------------------------


def _assert_balanced_latex_envs(tex: str) -> None:
    stack: list[str] = []
    for m in re.finditer(r"\\(begin|end)\{([^}]+)\}", tex):
        op, env = m.group(1), m.group(2)
        if op == "begin":
            stack.append(env)
        else:
            assert stack and stack[-1] == env, f"Unbalanced LaTeX env: end{{{env}}} vs stack={stack}"
            stack.pop()
    assert not stack, f"Unclosed LaTeX environments: {stack}"


def test_generate_latex_valid_syntax_and_refiner_guard(analyzed_db, tmp_path: Path) -> None:
    db_path, info = analyzed_db
    tex_path = tmp_path / "paper.tex"
    tex = generate_latex(db_path, output_path=tex_path, title="Synthetic RH Proof")

    assert tex_path.exists()
    assert r"\documentclass" in tex
    assert r"\begin{document}" in tex and r"\end{document}" in tex
    assert r"\leanlink{" in tex
    assert "DeadPkg.Unused" not in tex
    _assert_balanced_latex_envs(tex)
    assert detect_bookkeeping_leaks(tex) == []

    # Clean generated LaTeX must pass audit with 0 issues
    report = audit_latex(db_path, tex)
    assert report["passed"] is True, f"Clean LaTeX failed audit: {report['summary']}"
    assert report["fidelity_score"] == 1.0

    # Refiner guard rejects hallucinated leanlinks or bookkeeping leaks
    bad_calls = 0

    def _bad_refiner(draft: str, ctx: dict) -> str:
        nonlocal bad_calls
        bad_calls += 1
        return draft + r" \leanlink{Hallucinated.NonexistentTheorem}"

    tex_guarded = generate_latex(db_path, llm_refiner=_bad_refiner)
    assert bad_calls >= 1
    assert "Hallucinated.NonexistentTheorem" not in tex_guarded


def test_generate_blueprint_three_zoom_levels(analyzed_db, tmp_path: Path) -> None:
    db_path, _info = analyzed_db
    html_path = tmp_path / "blueprint.html"
    tex = generate_latex(db_path)
    aud = audit_latex(db_path, tex)
    html_text = generate_blueprint(
        db_path, output_path=html_path, title="Demo Blueprint", audit_report=aud
    )

    assert html_path.exists()
    assert "<!DOCTYPE html>" in html_text
    assert 'id="view-0"' in html_text
    assert 'id="view-1"' in html_text
    assert 'id="view-2"' in html_text
    assert "katex" in html_text.lower()
    assert "Demo Blueprint" in html_text
    assert "DeadPkg.Unused" not in html_text

    # Test convenience expose_all orchestrator
    out_dir = tmp_path / "expose_all_out"
    res = expose_all(db_path, out_dir, title="All In One")
    assert (out_dir / "paper.tex").exists()
    assert (out_dir / "blueprint.html").exists()
    assert (out_dir / "audit_report.json").exists()
    assert (out_dir / "audit_report.md").exists()
    assert res["audit_passed"] is True


# ---------------------------------------------------------------------------
# audit.py intentional mismatch detection tests
# ---------------------------------------------------------------------------


def test_audit_catches_all_intentional_mismatches(analyzed_db, tmp_path: Path) -> None:
    db_path, info = analyzed_db
    build_symbol_registry(db_path)

    # Inject a theorem with explicit hypotheses into the DB so we can test dropped-hypothesis detection
    from proof_compressor.schema import connect_db

    conn = connect_db(db_path)
    try:
        mod_id = conn.execute("SELECT id FROM modules WHERE path = 'Formalism.Seesaw'").fetchone()[0]
        conn.execute(
            """
            INSERT INTO declarations
            (name, short_name, module_id, kind, type_sig, canonical_type_hash, body_loc, is_mathlib, is_bookkeeping)
            VALUES (?, ?, ?, 'theorem', ?, 'h_hyp_test', 25, 0, 0)
            """,
            (
                "Formalism.Seesaw.prime_positive_bound",
                "prime_positive_bound",
                mod_id,
                "∀ p : ℕ, Nat.Prime p → p > 0 → BesselPeriod p ≠ 0",
            ),
        )
        new_id = conn.execute(
            "SELECT id FROM declarations WHERE name = 'Formalism.Seesaw.prime_positive_bound'"
        ).fetchone()[0]
        conn.execute(
            "INSERT INTO metrics (decl_id, reachable, in_degree, out_degree, bottleneck_score) VALUES (?, 1, 1, 1, 10.0)",
            (new_id,),
        )
        conn.commit()
    finally:
        conn.close()

    pillar0 = info["pillars"][0]  # GroundTheory.ThetaLift.thetalift_main_bound
    pillar1 = info["pillars"][1]  # Formalism.Seesaw.seesaw_main_bound (depends on pillar0!)
    pillar3 = info["pillars"][3]  # Development.IwasawaTower.iwasawatower_main_bound (NOT a dep of pillar0!)
    dead0 = info["dead"][0]

    sabotaged_tex = rf"""\documentclass{{amsart}}
\newcommand{{\leanlink}}[1]{{\texttt{{\detokenize{{#1}}}}}}
\begin{{document}}

\section{{Sabotaged Exposition}}

% 1. Unknown leanlink + unreachable dead leanlink
We mention an unknown lemma~\leanlink{{Bogus.InventedTheorem}} and a dead lemma~\leanlink{{{dead0}}}.

% 2. Invented / non-DAG citation: pillar0 does NOT depend on pillar3
\begin{{theorem}}[Pillar Zero]\leanlink{{{pillar0}}}
\[
\forall m \in \mathbb{{N}}, \; m \neq 0
\]
\end{{theorem}}
\begin{{proof}}
This follows from the unrelated downstream result~\leanlink{{{pillar3}}}.
\end{{proof}}

% 3. Omitted high-bottleneck dependency: pillar1 depends directly on pillar0, omitted from proof
\begin{{theorem}}[Pillar One]\leanlink{{{pillar1}}}
\[
\forall m \in \mathbb{{N}}, \; m \neq 0
\]
\end{{theorem}}
\begin{{proof}}
This follows trivially without citing its main bottleneck prerequisite.
\end{{proof}}

% 4. Dropped hypothesis: omits Prime and > 0 and \neq from statement
\begin{{theorem}}[Prime Bound]\leanlink{{Formalism.Seesaw.prime_positive_bound}}
\[
\text{{The Bessel period holds for every integer }} p.
\]
\end{{theorem}}

% 5. Symbol drift + bookkeeping leak
Using the unregistered macro $\UnregisteredFooMacro$, because the reals are totally ordered,
we apply Finset.sum and Nat.cast coercion.

\end{{document}}
"""

    aud_json = tmp_path / "sabotaged_audit.json"
    aud_md = tmp_path / "sabotaged_audit.md"
    report = audit_latex(
        db_path,
        sabotaged_tex,
        output_json=aud_json,
        output_md=aud_md,
        bottleneck_threshold=0.01,
    )

    assert report["passed"] is False
    assert report["fidelity_score"] < 1.0
    assert aud_json.exists() and aud_md.exists()

    # Verify EVERY intentional mismatch category was caught!
    assert any(x["constant"] == "Bogus.InventedTheorem" for x in report["unknown_leanlinks"])
    assert any(x["constant"] == dead0 for x in report["unreachable_leanlinks"])
    assert any(
        x["theorem"] == pillar0 and x["cited"] == pillar3
        for x in report["invented_citations"]
    )
    assert any(
        x["theorem"] == pillar1 and x["missing_dependency"] == pillar0
        for x in report["omitted_bottlenecks"]
    )
    assert any(
        x["theorem"] == "Formalism.Seesaw.prime_positive_bound"
        for x in report["dropped_hypotheses"]
    )
    assert any(x["macro"] == r"\UnregisteredFooMacro" for x in report["symbol_drift"])
    assert len(report["bookkeeping_leaks"]) >= 2

    md = format_audit_markdown(report)
    assert "FAIL" in md
    assert "Bogus.InventedTheorem" in md


# ---------------------------------------------------------------------------
# refactor/planner.py & gate.py tests
# ---------------------------------------------------------------------------


def test_refactor_planner_work_orders(analyzed_db, tmp_path: Path) -> None:
    db_path, _info = analyzed_db
    out_json = tmp_path / "refactor.json"
    orders = plan_refactors(db_path, top_k=10, min_loc=20, output_path=out_json)

    assert len(orders) >= 1
    assert out_json.exists()
    first = orders[0]
    assert first["internal_loc"] >= 20
    assert first["interface_width"] >= 1
    assert len(first["interface_out"]) >= 1
    assert len(first["verification_checklist"]) >= 2

    md = format_refactor_plan_markdown(orders)
    assert "# Kernel-Checked Refactoring Plan" in md
    assert first["order_id"] in md


def test_refactor_gate_loc_axioms_build_and_real_lake(tmp_path: Path) -> None:
    # 1. Effective LOC counting with nested comments & blank lines
    lean_src = """\
-- line comment
/- outer
   /- nested -/
   still comment -/

def foo (n : Nat) : Nat :=
  n + 1 -- trailing comment
"""
    assert count_effective_loc(lean_src) == 2

    # 2. Axiom and signature parsing
    ax_out = (
        "'Foo.thm1' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        "'Foo.thm2' does not depend on any axioms\n"
        "'Foo.bad' depends on axioms: [sorryAx]\n"
    )
    parsed_ax = parse_print_axioms(ax_out)
    assert parsed_ax["Foo.thm1"] == ["propext", "Classical.choice", "Quot.sound"]
    assert parsed_ax["Foo.thm2"] == []
    assert parsed_ax["Foo.bad"] == ["sorryAx"]

    sig_out = "@Foo.thm1 : ∀ n : Nat, n = n\n"
    assert parse_check_signatures(sig_out)["Foo.thm1"] == "∀ n : Nat, n = n"

    # 3. Mocked command runner tests (pass, sorryAx fail, LOC fail, build fail)
    def _ok_runner(cmd, cwd, env, timeout_s):
        if "build" in cmd:
            return (0, "build ok", "")
        return (
            0,
            "@Foo.thm : True\n'Foo.thm' depends on axioms: [propext, Classical.choice]\n",
            "",
        )

    res_ok = verify_refactor_gate(
        tmp_path,
        target_modules=["Foo"],
        exported_decls=["Foo.thm"],
        expected_signatures={"Foo.thm": "True"},
        before_loc=120,
        after_loc=80,
        command_runner=_ok_runner,
    )
    assert res_ok.passed is True
    assert res_ok.loc_check["reduction"] == 40

    # Fail on zero LOC reduction
    res_no_red = verify_refactor_gate(
        tmp_path,
        before_loc=100,
        after_loc=100,
        run_lake=False,
    )
    assert res_no_red.passed is False
    assert res_no_red.loc_check["passed"] is False

    # Fail on sorryAx
    def _sorry_runner(cmd, cwd, env, timeout_s):
        if "build" in cmd:
            return (0, "ok", "")
        return (0, "'Foo.thm' depends on axioms: [propext, sorryAx]\n", "")

    res_sorry = verify_refactor_gate(
        tmp_path,
        exported_decls=["Foo.thm"],
        before_loc=100,
        after_loc=50,
        command_runner=_sorry_runner,
    )
    assert res_sorry.passed is False
    assert "sorryAx" in " ".join(res_sorry.errors)

    # 4. Real lake execution check against lean_extractor/
    repo_root = Path(__file__).resolve().parent.parent
    lean_dir = repo_root / "lean_extractor"
    lake_bin = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if lean_dir.exists() and Path(lake_bin).exists():
        res_real = verify_refactor_gate(
            lean_dir,
            target_modules=["ExtractDag"],
            exported_decls=["ExtractDag.demoTheorem"],
            before_loc=50,
            after_loc=30,
            run_lake=True,
            lake_bin=lake_bin,
        )
        assert res_real.passed is True, f"Real lake gate failed: {res_real.errors}"
        assert res_real.build_check["passed"] is True
        assert res_real.axiom_check["passed"] is True
