"""Shared pytest fixtures for proof-compressor verification suite."""

from __future__ import annotations

import io
import json
import sqlite3
import tarfile
from pathlib import Path
from typing import Any

import pytest

from proof_compressor.schema import (
    batch_insert_declarations,
    batch_insert_edges,
    batch_insert_module_imports,
    batch_insert_modules,
    init_db,
    set_meta,
)


@pytest.fixture
def mem_db() -> sqlite3.Connection:
    """In-memory SQLite DB initialized with the proof-compressor schema."""
    conn = init_db(":memory:")
    yield conn
    conn.close()


@pytest.fixture
def tmp_db_path(tmp_path: Path) -> Path:
    """Path for a temporary on-disk SQLite DB."""
    return tmp_path / "test_proof.db"


SAMPLE_LEAN_PROJECT: dict[str, str] = {
    "lean/lean-toolchain": "leanprover/lean4:v4.33.1\n",
    "lean/lakefile.toml": 'name = "demo"\nsrcDir = "src"\n',
    "lean/src/Statements.lean": """\
import Mathlib

/-- The main target statement for our demo proof. -/
def MainConjecture : Prop := ∀ n : ℕ, n ≥ 0
""",
    "lean/src/GroundTheory/ThetaLift.lean": """\
import Mathlib

namespace GroundTheory

/-- Unitary theta lift kernel between definite unitary groups. -/
def ThetaKernel (m : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ m

/-- Non-trivial core estimate on the iterated theta lift norm. -/
theorem theta_lift_norm_bound
    (m : ℕ)
    (hm : m > 0)
    (x : ℝ) :
    ‖ThetaKernel m x‖ ≥ 0 := by
  have h1 : 0 ≤ ‖ThetaKernel m x‖ := norm_nonneg _
  exact h1

/-- Trivial bookkeeping coercion helper. -/
lemma nat_cast_nonneg_aux (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := by
  exact Nat.cast_nonneg n

end GroundTheory
""",
    "lean/src/Formalism/Seesaw.lean": """\
import GroundTheory.ThetaLift

namespace Formalism.Seesaw

open GroundTheory

/-- Bessel period extracted via the seesaw identity. -/
def BesselPeriod (m : ℕ) : ℝ :=
  ‖ThetaKernel m 1‖

/-- Seesaw identity linking iterated theta lift to a Bessel period. -/
theorem seesaw_bessel_identity (m : ℕ) (hm : m > 0) :
    BesselPeriod m ≥ 0 := by
  unfold BesselPeriod
  exact theta_lift_norm_bound m hm 1

/-- Duplicate lemma with alpha-equivalent type signature to theta_lift_norm_bound. -/
theorem theta_lift_norm_bound_dup
    (k : ℕ)
    (hk : k > 0)
    (y : ℝ) :
    ‖ThetaKernel k y‖ ≥ 0 := by
  exact theta_lift_norm_bound k hk y

end Formalism.Seesaw
""",
    "lean/src/Supplements/MainTheorems.lean": """\
import Statements
import Formalism.Seesaw

/-- Re-export barrel connecting the seesaw pillar to the final theorem. -/
theorem main_conjecture_proof : MainConjecture := by
  intro n
  have h := Formalism.Seesaw.seesaw_bessel_identity 1 (by omega)
  exact Nat.zero_le n
""",
    "lean/src/Main.lean": """\
import Statements
import Supplements.MainTheorems

/-- Root theorem of the repository. -/
theorem RH_demo : MainConjecture := main_conjecture_proof
""",
    "lean/src/DeadBranch/Unused.lean": """\
import Mathlib

namespace DeadBranch

/-- Completely unreachable exploration code. -/
def DeadObj (x : ℕ) : ℕ := x + 1

theorem dead_theorem (x : ℕ) : DeadObj x = x + 1 := rfl

end DeadBranch
""",
}


def make_tar_gz_bytes(files: dict[str, str]) -> bytes:
    """Build an in-memory .tar.gz archive containing the given path -> text map."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz") as tf:
        for rel_path, content in files.items():
            raw = content.encode("utf-8")
            info = tarfile.TarInfo(name=rel_path)
            info.size = len(raw)
            tf.addfile(info, io.BytesIO(raw))
    return buf.getvalue()


@pytest.fixture
def sample_lean_dir(tmp_path: Path) -> Path:
    """Write SAMPLE_LEAN_PROJECT as a directory tree on disk."""
    root = tmp_path / "sample_proj"
    for rel_path, content in SAMPLE_LEAN_PROJECT.items():
        p = root / rel_path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    return root / "lean"


@pytest.fixture
def sample_tar_gz(tmp_path: Path) -> Path:
    """Create a single .tar.gz archive of SAMPLE_LEAN_PROJECT."""
    archive = tmp_path / "sample.tar.gz"
    archive.write_bytes(make_tar_gz_bytes(SAMPLE_LEAN_PROJECT))
    return archive


@pytest.fixture
def sample_multipart_tar_gz(tmp_path: Path) -> list[Path]:
    """Create a 3-part split .tar.gz.part01..part03 archive of SAMPLE_LEAN_PROJECT."""
    raw = make_tar_gz_bytes(SAMPLE_LEAN_PROJECT)
    chunk = max(1, len(raw) // 3)
    parts: list[Path] = []
    slices = [raw[:chunk], raw[chunk : 2 * chunk], raw[2 * chunk :]]
    for idx, data in enumerate(slices, start=1):
        p = tmp_path / f"lean.tar.gz.part{idx:02d}"
        p.write_bytes(data)
        parts.append(p)
    return parts


def build_synthetic_dag_db(
    db_path: str | Path = ":memory:",
    *,
    num_pillars: int = 5,
    leaves_per_pillar: int = 40,
    dead_nodes: int = 100,
    include_cycle: bool = True,
    include_duplicates: bool = True,
) -> tuple[sqlite3.Connection, dict[str, Any]]:
    """Build a realistic synthetic multi-module proof DAG directly in SQLite.

    Structure:
      - Root theorem `Main.RH` depends on a chain/diamond of `num_pillars` bottleneck theorems.
      - Each pillar depends on a subtree of `leaves_per_pillar` helper lemmas (some bookkeeping,
        some duplicate canonical hashes) + a core definition + a Mathlib boundary lemma.
      - `dead_nodes` unreachable declarations in `DeadPkg.Unused` (to verify exact pruning).
      - Optional mutual-recursion 3-cycle in one module (to test Tarjan SCC).
    """
    conn = init_db(db_path)

    modules: list[tuple[str, str, int, int]] = [
        ("Main", "Main", 20, 0),
        ("Mathlib.Analysis.Zeta", "Mathlib", 1000, 1),
        ("DeadPkg.Unused", "DeadPkg", dead_nodes * 10, 0),
    ]
    pillar_names = [
        ("GroundTheory.ThetaLift", "GroundTheory", "ThetaLift"),
        ("Formalism.Seesaw", "Formalism", "Seesaw"),
        ("Formalism.BostSlope", "Formalism", "BostSlope"),
        ("Development.IwasawaTower", "Development", "IwasawaTower"),
        ("Development.VandiverCohomology", "Development", "VandiverCohomology"),
    ]
    for i in range(num_pillars):
        if i < len(pillar_names):
            mod_path, pkg, _ = pillar_names[i]
        else:
            mod_path, pkg = f"Pkg{i}.Stage{i}", f"Pkg{i}"
        modules.append((mod_path, pkg, (leaves_per_pillar + 5) * 15, 0))

    batch_insert_modules(conn, modules)
    conn.commit()
    mod_id_by_path = {
        r["path"]: r["id"]
        for r in conn.execute("SELECT id, path FROM modules").fetchall()
    }

    decls: list[tuple[Any, ...]] = []
    # Mathlib boundary decls
    mathlib_mod = mod_id_by_path["Mathlib.Analysis.Zeta"]
    decls.append((
        "Mathlib.riemannZeta_ne_zero",
        "riemannZeta_ne_zero",
        mathlib_mod,
        "theorem",
        "∀ s : ℂ, s.re > 1 → riemannZeta s ≠ 0",
        "hash_mathlib_zeta",
        5,
        100,
        "Nonvanishing of zeta for Re(s) > 1.",
        1,
        0,
        1,
        5,
        json.dumps(["propext", "Classical.choice"]),
    ))
    decls.append((
        "Mathlib.InternalUnusedHelper",
        "InternalUnusedHelper",
        mathlib_mod,
        "lemma",
        "True",
        "hash_mathlib_internal",
        2,
        10,
        "",
        1,
        1,
        10,
        12,
        None,
    ))

    # Root theorem
    main_mod = mod_id_by_path["Main"]
    decls.append((
        "Main.RH",
        "RH",
        main_mod,
        "theorem",
        "∀ s : ℂ, riemannZeta s = 0 → s.re = 1/2",
        "hash_root_rh",
        15,
        500,
        "Riemann Hypothesis main theorem.",
        0,
        0,
        1,
        15,
        json.dumps(["propext", "Classical.choice", "Quot.sound"]),
    ))

    pillar_decl_names: list[str] = []
    pillar_def_names: list[str] = []
    edges_by_name: list[tuple[str, str, str]] = []

    for i in range(num_pillars):
        if i < len(pillar_names):
            mod_path, _, label = pillar_names[i]
        else:
            mod_path, label = f"Pkg{i}.Stage{i}", f"Stage{i}"
        mid = mod_id_by_path[mod_path]

        def_name = f"{mod_path}.{label}Operator"
        pillar_name = f"{mod_path}.{label.lower()}_main_bound"
        pillar_def_names.append(def_name)
        pillar_decl_names.append(pillar_name)

        decls.append((
            def_name,
            f"{label}Operator",
            mid,
            "def",
            "ℕ → ℂ → ℂ",
            f"hash_def_{i}",
            12,
            80,
            f"Core mathematical object for {label}.",
            0,
            0,
            1,
            12,
            None,
        ))
        decls.append((
            pillar_name,
            f"{label.lower()}_main_bound",
            mid,
            "theorem",
            f"∀ m : ℕ, {def_name} m 1 ≠ 0",
            f"hash_pillar_{i}",
            40,
            1200,
            f"Main bottleneck theorem for {label}.",
            0,
            0,
            15,
            55,
            json.dumps(["propext", "Classical.choice"]),
        ))
        edges_by_name.append((pillar_name, def_name, "type"))
        edges_by_name.append((pillar_name, "Mathlib.riemannZeta_ne_zero", "proof"))

        # Chain pillars so earlier pillars feed later ones and all feed Main.RH
        if i > 0:
            edges_by_name.append((pillar_name, pillar_decl_names[i - 1], "proof"))

        # Subtree of helpers beneath each pillar
        prev_helper: str | None = None
        for j in range(leaves_per_pillar):
            is_bk = 1 if (j % 5 == 0) else 0
            hname = f"{mod_path}.helper_{j}" if not is_bk else f"{mod_path}.cast_nonneg_aux_{j}"
            # Intentional duplicates across pillars for j == 1, 2
            if include_duplicates and j in (1, 2):
                chash = f"hash_dup_shared_{j}"
                tsig = f"∀ x : ℝ, x ^ {j + 1} ≥ 0"
            else:
                chash = f"hash_helper_{i}_{j}"
                tsig = f"∀ n : ℕ, n + {i * 100 + j} ≥ 0"
            decls.append((
                hname,
                hname.split(".")[-1],
                mid,
                "lemma",
                tsig,
                chash,
                10 + (j % 7),
                40 + j,
                "" if is_bk else f"Helper estimate {j} in {label}.",
                0,
                is_bk,
                60 + j * 12,
                70 + j * 12,
                None,
            ))
            edges_by_name.append((pillar_name, hname, "proof"))
            edges_by_name.append((hname, def_name, "ref"))
            if prev_helper is not None and j % 3 != 0:
                edges_by_name.append((hname, prev_helper, "proof"))
            prev_helper = hname

    # Root depends on final pillar (and also directly on pillar 0 to form a diamond)
    edges_by_name.append(("Main.RH", pillar_decl_names[-1], "proof"))
    if num_pillars >= 2:
        edges_by_name.append(("Main.RH", pillar_decl_names[0], "proof"))

    # Optional 3-cycle in pillar 0 module
    cycle_names: list[str] = []
    if include_cycle:
        mid0 = mod_id_by_path[pillar_names[0][0]]
        for c in range(3):
            cname = f"{pillar_names[0][0]}.mutual_rec_{c}"
            cycle_names.append(cname)
            decls.append((
                cname,
                f"mutual_rec_{c}",
                mid0,
                "lemma",
                f"∀ n : ℕ, n + {c} = {c} + n",
                f"hash_cycle_{c}",
                8,
                30,
                "Mutually recursive helper.",
                0,
                0,
                900 + c * 10,
                908 + c * 10,
                None,
            ))
        edges_by_name.append((pillar_decl_names[0], cycle_names[0], "proof"))
        edges_by_name.append((cycle_names[0], cycle_names[1], "proof"))
        edges_by_name.append((cycle_names[1], cycle_names[2], "proof"))
        edges_by_name.append((cycle_names[2], cycle_names[0], "proof"))

    # Mathlib internal edge (should NOT be expanded if boundary stops at Mathlib)
    edges_by_name.append(("Mathlib.riemannZeta_ne_zero", "Mathlib.InternalUnusedHelper", "proof"))

    # Dead nodes
    dead_mod = mod_id_by_path["DeadPkg.Unused"]
    dead_decl_names: list[str] = []
    for d in range(dead_nodes):
        dname = f"DeadPkg.Unused.dead_lemma_{d}"
        dead_decl_names.append(dname)
        decls.append((
            dname,
            f"dead_lemma_{d}",
            dead_mod,
            "lemma",
            f"∀ x : ℕ, x = x ∧ {d} = {d}",
            f"hash_dead_{d}",
            10,
            20,
            "Unreachable dead code.",
            0,
            0,
            1 + d * 10,
            10 + d * 10,
            None,
        ))
        if d > 0:
            edges_by_name.append((dname, dead_decl_names[d - 1], "proof"))

    batch_insert_declarations(conn, decls)
    conn.commit()

    decl_id_by_name = {
        r["name"]: r["id"]
        for r in conn.execute("SELECT id, name FROM declarations").fetchall()
    }
    edge_rows = [
        (decl_id_by_name[s], decl_id_by_name[t], k)
        for s, t, k in edges_by_name
    ]
    batch_insert_edges(conn, edge_rows)

    # Module imports
    last_pillar_mod = (
        pillar_names[num_pillars - 1][0]
        if num_pillars - 1 < len(pillar_names)
        else f"Pkg{num_pillars - 1}.Stage{num_pillars - 1}"
    )
    mod_imports = [
        (main_mod, last_pillar_mod, mod_id_by_path[last_pillar_mod]),
    ]
    for i in range(1, num_pillars):
        cur_p = pillar_names[i][0] if i < len(pillar_names) else f"Pkg{i}.Stage{i}"
        prev_p = pillar_names[i - 1][0] if (i - 1) < len(pillar_names) else f"Pkg{i-1}.Stage{i-1}"
        mod_imports.append((mod_id_by_path[cur_p], prev_p, mod_id_by_path[prev_p]))
    batch_insert_module_imports(conn, mod_imports)
    set_meta(conn, "source", "synthetic_test")
    conn.commit()

    info = {
        "root": "Main.RH",
        "pillars": pillar_decl_names,
        "defs": pillar_def_names,
        "cycle": cycle_names,
        "dead": dead_decl_names,
        "mathlib_boundary": "Mathlib.riemannZeta_ne_zero",
        "mathlib_internal": "Mathlib.InternalUnusedHelper",
    }
    return conn, info
