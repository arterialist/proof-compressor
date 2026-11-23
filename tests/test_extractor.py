"""Comprehensive tests for proof_compressor.ingest and lean_extractor."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from proof_compressor.ingest.lean_parser import (
    canonical_type_hash,
    canonicalize_type,
    is_bookkeeping_decl,
    normalize_module_path,
    parse_lean_source,
    strip_comments_and_extract_docstrings,
)
from proof_compressor.ingest.olean_bridge import ingest_olean_jsonl
from proof_compressor.ingest.stream_archive import (
    ConcatenatedFileReader,
    ingest_source,
    resolve_input_source,
)
from proof_compressor.schema import connect_db


# ---------------------------------------------------------------------------
# lean_parser tests
# ---------------------------------------------------------------------------


def test_normalize_module_path() -> None:
    assert normalize_module_path("lean/src/Development/WeilBound/Core.lean") == (
        "Development.WeilBound.Core",
        "Development",
        False,
    )
    assert normalize_module_path("lean/src/Main.lean") == ("Main", "Main", False)
    assert normalize_module_path(
        "./.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean"
    ) == ("Mathlib.NumberTheory.LSeries.RiemannZeta", "Mathlib", True)
    assert normalize_module_path("Init/Data/Nat/Basic.lean") == (
        "Init.Data.Nat.Basic",
        "Init",
        True,
    )


def test_strip_nested_comments_and_docstrings() -> None:
    src = """\
/- outer comment
   /- nested comment with theorem fake : True := trivial -/
   still outer -/
/-- Docstring for real_thm. -/
theorem real_thm : String := "-- not a comment /- neither -/" -- trailing comment
"""
    cleaned, docs = strip_comments_and_extract_docstrings(src)
    assert "fake" not in cleaned
    assert '"-- not a comment /- neither -/"' in cleaned
    assert "trailing comment" not in cleaned
    assert len(cleaned.splitlines()) == len(src.splitlines())
    assert 4 in docs
    assert "Docstring for real_thm." in docs[4]


def test_canonical_type_hash_alpha_equivalence() -> None:
    t1 = "(x : ℝ) (hx : x > 0) -> forall (n : ℕ), x ^ n > 0"
    t2 = "(y : ℝ)   (hy : y > 0) → ∀ (k : ℕ), y ^ k > 0"
    t3 = "(x : ℝ) (hx : x > 0) → ∀ (n : ℕ), x ^ n ≥ 0"

    assert canonicalize_type(t1) == canonicalize_type(t2)
    assert canonical_type_hash(t1) == canonical_type_hash(t2)
    assert canonical_type_hash(t1) != canonical_type_hash(t3)
    assert len(canonical_type_hash(t1)) == 24
    assert canonical_type_hash("") == ""


def test_parse_lean_source_namespaces_docstrings_multiline_bookkeeping() -> None:
    src = """\
import Mathlib
import GroundTheory.ThetaLift

namespace Outer.Inner

open GroundTheory

/-- Multiline docstring
    attached across attributes. -/
@[simp]
noncomputable theorem main_estimate
    (m : ℕ)
    (hm : m > 0) :
    ∀ x : ℝ, ThetaKernel m x = ThetaKernel m x := by
  intro x
  rfl

/-- Trivial measurability glue. -/
lemma theta_measurable (m : ℕ) : Measurable (ThetaKernel m) := by
  measurability

instance instInhabitedDemo : Inhabited ℕ := ⟨0⟩

structure LiftData where
  rank : ℕ
  weight : ℝ

end Inner

theorem outer_thm : Outer.Inner.LiftData := { rank := 1, weight := 0 }

end Outer

theorem UpperTheory.FinalTheorems.everyCharacter : Prop := True
"""
    parsed = parse_lean_source(src, "Formalism.TestMod")
    assert parsed.imports == ["Mathlib", "GroundTheory.ThetaLift"]
    by_name = {d.name: d for d in parsed.declarations}

    assert "Outer.Inner.main_estimate" in by_name
    est = by_name["Outer.Inner.main_estimate"]
    assert est.kind == "theorem"
    assert est.docstring is not None and "Multiline docstring" in est.docstring
    assert "ThetaKernel" in est.type_refs
    assert est.is_bookkeeping is False
    assert est.namespace_stack == ("Outer", "Inner")
    assert "GroundTheory" in est.open_namespaces

    assert "Outer.Inner.theta_measurable" in by_name
    assert by_name["Outer.Inner.theta_measurable"].is_bookkeeping is True

    assert "Outer.Inner.instInhabitedDemo" in by_name
    assert by_name["Outer.Inner.instInhabitedDemo"].is_bookkeeping is True

    assert "Outer.Inner.LiftData" in by_name
    assert by_name["Outer.Inner.LiftData"].kind == "structure"
    assert by_name["Outer.Inner.LiftData"].is_bookkeeping is False

    # Partial `end Inner` should leave `Outer` active
    assert "Outer.outer_thm" in by_name
    assert "Outer.Inner.LiftData" in by_name["Outer.outer_thm"].type_refs

    # Qualified dotted declaration without active namespace
    assert "UpperTheory.FinalTheorems.everyCharacter" in by_name
    assert by_name["UpperTheory.FinalTheorems.everyCharacter"].short_name == "everyCharacter"


def test_bookkeeping_classifier_edge_cases() -> None:
    assert is_bookkeeping_decl("instance", "instFoo", "Foo ℕ", ":= ⟨⟩", 1) is True
    assert is_bookkeeping_decl("lemma", "foo_cast_eq", ": (n : ℝ) = n", ":= by rfl", 1) is True
    assert is_bookkeeping_decl("theorem", "trivial_bound", ": 1 ≤ 2", ":= by norm_num", 1) is True
    assert (
        is_bookkeeping_decl(
            "theorem",
            "bost_slope_inequality",
            "(E : HermitianBundle) : deg E ≤ slope E",
            ":= by\n  have h1 := ...\n  have h2 := ...\n  exact h2",
            25,
        )
        is False
    )


# ---------------------------------------------------------------------------
# stream_archive tests (dir, single tar.gz, multi-part tar.gz, zero extraction)
# ---------------------------------------------------------------------------


def _assert_sample_db_contents(db_path: Path) -> None:
    conn = connect_db(db_path, readonly=True)
    try:
        mods = {r["path"] for r in conn.execute("SELECT path FROM modules").fetchall()}
        assert {
            "Statements",
            "GroundTheory.ThetaLift",
            "Formalism.Seesaw",
            "Supplements.MainTheorems",
            "Main",
            "DeadBranch.Unused",
        } == mods

        decls = {
            r["name"]: dict(r)
            for r in conn.execute("SELECT * FROM declarations").fetchall()
        }
        assert "RH_demo" in decls
        assert "main_conjecture_proof" in decls
        assert "Formalism.Seesaw.seesaw_bessel_identity" in decls
        assert "GroundTheory.theta_lift_norm_bound" in decls
        assert "DeadBranch.dead_theorem" in decls

        # Alpha-equivalent duplicate hash check
        assert (
            decls["GroundTheory.theta_lift_norm_bound"]["canonical_type_hash"]
            == decls["Formalism.Seesaw.theta_lift_norm_bound_dup"]["canonical_type_hash"]
        )
        assert decls["GroundTheory.nat_cast_nonneg_aux"]["is_bookkeeping"] == 1
        assert decls["Formalism.Seesaw.seesaw_bessel_identity"]["is_bookkeeping"] == 0

        # Check transitive dependency edges across modules
        edge_pairs = {
            (r["src_name"], r["dst_name"], r["kind"])
            for r in conn.execute(
                """
                SELECT s.name AS src_name, d.name AS dst_name, e.kind
                FROM edges e
                JOIN declarations s ON s.id = e.src_id
                JOIN declarations d ON d.id = e.dst_id
                """
            ).fetchall()
        }
        assert ("RH_demo", "MainConjecture", "type") in edge_pairs
        assert ("RH_demo", "main_conjecture_proof", "proof") in edge_pairs
        assert (
            "main_conjecture_proof",
            "Formalism.Seesaw.seesaw_bessel_identity",
            "proof",
        ) in edge_pairs
        assert (
            "Formalism.Seesaw.seesaw_bessel_identity",
            "GroundTheory.theta_lift_norm_bound",
            "proof",
        ) in edge_pairs
    finally:
        conn.close()


def test_ingest_directory_source(sample_lean_dir: Path, tmp_path: Path) -> None:
    db = tmp_path / "dir.db"
    stats = ingest_source(sample_lean_dir, db)
    assert stats.files_ingested == 6
    assert stats.modules_inserted == 6
    assert stats.edges_inserted >= 6
    _assert_sample_db_contents(db)


def test_ingest_single_tar_gz_zero_extraction(
    sample_tar_gz: Path, tmp_path: Path
) -> None:
    work = tmp_path / "run_tar"
    work.mkdir()
    db = work / "tar.db"
    stats = ingest_source(sample_tar_gz, db)
    assert stats.files_ingested == 6
    # Verify zero .lean files were extracted to disk
    assert list(work.rglob("*.lean")) == []
    _assert_sample_db_contents(db)


def test_ingest_multipart_tar_gz_autodiscovery_and_glob(
    sample_multipart_tar_gz: list[Path], tmp_path: Path
) -> None:
    part01 = sample_multipart_tar_gz[0]
    kind, resolved = resolve_input_source(part01)
    assert kind == "archive"
    assert len(resolved) == 3

    # Verify ConcatenatedFileReader reads exact total bytes
    expected_bytes = sum(p.stat().st_size for p in sample_multipart_tar_gz)
    with ConcatenatedFileReader(sample_multipart_tar_gz) as r:
        data = r.read()
        assert len(data) == expected_bytes
        assert r.bytes_read == expected_bytes

    db1 = tmp_path / "part01.db"
    s1 = ingest_source(part01, db1)
    assert s1.files_ingested == 6
    _assert_sample_db_contents(db1)

    glob_pat = str(part01.parent / "lean.tar.gz.part*")
    db2 = tmp_path / "glob.db"
    s2 = ingest_source(glob_pat, db2)
    assert s2.files_ingested == 6
    _assert_sample_db_contents(db2)

    # Zero extracted .lean files anywhere in parent directory
    assert list(tmp_path.rglob("*.lean")) == []


def test_ingest_max_files_and_path_filter(
    sample_tar_gz: Path, tmp_path: Path
) -> None:
    db_max = tmp_path / "max2.db"
    s_max = ingest_source(sample_tar_gz, db_max, max_files=2)
    assert s_max.files_ingested == 2

    db_filt = tmp_path / "filt.db"
    s_filt = ingest_source(sample_tar_gz, db_filt, path_filter=r"Formalism|Main")
    assert s_filt.files_ingested == 3


# ---------------------------------------------------------------------------
# olean_bridge + lean_extractor tests
# ---------------------------------------------------------------------------


def test_olean_bridge_fresh_and_merge(sample_tar_gz: Path, tmp_path: Path) -> None:
    jsonl = tmp_path / "kernel.jsonl"
    records = [
        {
            "name": "RH_demo",
            "module": "Main",
            "kind": "thm",
            "type": "MainConjecture",
            "proof_term_size": 42,
            "is_mathlib": False,
            "axioms": ["propext", "Classical.choice"],
            "type_deps": ["MainConjecture"],
            "value_deps": ["main_conjecture_proof", "Mathlib.Analysis.FakeBoundary"],
        },
        {
            "name": "Main.NewKernelLemma",
            "module": "Main",
            "kind": "theorem",
            "type": "True",
            "proof_term_size": 7,
            "is_mathlib": False,
            "axioms": [],
            "type_deps": [],
            "value_deps": [],
        },
    ]
    jsonl.write_text("\n".join(json.dumps(r) for r in records) + "\n", encoding="utf-8")

    # 1. Fresh ingest
    db_fresh = tmp_path / "olean_fresh.db"
    st_fresh = ingest_olean_jsonl(jsonl, db_fresh, merge=False)
    assert st_fresh.records_read == 2
    assert st_fresh.declarations_inserted == 2
    assert st_fresh.boundary_stubs_inserted >= 2
    assert st_fresh.edges_inserted == 3

    # 2. Merge onto source-ingested DB
    db_merge = tmp_path / "olean_merge.db"
    ingest_source(sample_tar_gz, db_merge)
    st_merge = ingest_olean_jsonl(jsonl, db_merge, merge=True)
    assert st_merge.declarations_updated == 1
    assert st_merge.declarations_inserted == 1

    conn = connect_db(db_merge, readonly=True)
    try:
        row = conn.execute(
            "SELECT proof_term_size, axioms_json FROM declarations WHERE name = 'RH_demo'"
        ).fetchone()
        assert row["proof_term_size"] == 42
        assert json.loads(row["axioms_json"]) == ["propext", "Classical.choice"]

        stub = conn.execute(
            "SELECT is_mathlib FROM declarations WHERE name = 'Mathlib.Analysis.FakeBoundary'"
        ).fetchone()
        assert stub is not None and stub["is_mathlib"] == 1
    finally:
        conn.close()


def test_lean_extractor_lake_build_and_selftest(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parent.parent
    lean_dir = repo_root / "lean_extractor"
    if not lean_dir.exists():
        pytest.skip("lean_extractor directory not found")

    lake_bin = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if not Path(lake_bin).exists():
        pytest.skip("lake binary not installed")

    env = os.environ.copy()
    elan_bin = str(Path.home() / ".elan" / "bin")
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

    # Verify lake build succeeds
    build_proc = subprocess.run(
        [lake_bin, "build"],
        cwd=lean_dir,
        env=env,
        capture_output=True,
        text=True,
        timeout=180,
    )
    assert build_proc.returncode == 0, f"lake build failed:\n{build_proc.stderr}\n{build_proc.stdout}"

    # Run --self-test and ingest JSONL via olean_bridge
    out_jsonl = tmp_path / "selftest.jsonl"
    run_proc = subprocess.run(
        [
            lake_bin,
            "env",
            ".lake/build/bin/extract_dag",
            "--self-test",
            "--out",
            str(out_jsonl),
        ],
        cwd=lean_dir,
        env=env,
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert run_proc.returncode == 0, f"extract_dag failed:\n{run_proc.stderr}"
    assert out_jsonl.exists() and out_jsonl.stat().st_size > 0

    db_path = tmp_path / "selftest.db"
    stats = ingest_olean_jsonl(out_jsonl, db_path, merge=False)
    assert stats.records_read >= 3
    assert stats.edges_inserted >= 2

    conn = connect_db(db_path, readonly=True)
    try:
        decls = {
            r["name"]: dict(r)
            for r in conn.execute("SELECT * FROM declarations").fetchall()
        }
        assert "ExtractDag.demoTheorem" in decls
        assert "ExtractDag.demoHelper_eq" in decls
        assert "ExtractDag.demoHelper" in decls
        assert decls["ExtractDag.demoTheorem"]["proof_term_size"] > 0
        assert decls["ExtractDag.demoTheorem"]["axioms_json"] is not None

        edge_pairs = {
            (r["src_name"], r["dst_name"])
            for r in conn.execute(
                """
                SELECT s.name AS src_name, d.name AS dst_name
                FROM edges e
                JOIN declarations s ON s.id = e.src_id
                JOIN declarations d ON d.id = e.dst_id
                """
            ).fetchall()
        }
        assert ("ExtractDag.demoTheorem", "ExtractDag.demoHelper_eq") in edge_pairs
        assert ("ExtractDag.demoTheorem", "ExtractDag.demoHelper") in edge_pairs
    finally:
        conn.close()
