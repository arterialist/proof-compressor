"""Tests for proof_compressor.schema SQLite contract and bulk helpers."""

from __future__ import annotations

import sqlite3
from pathlib import Path

import pytest

from proof_compressor.schema import (
    SCHEMA_VERSION,
    batch_insert_declarations,
    batch_insert_edges,
    batch_insert_module_imports,
    batch_insert_modules,
    connect_db,
    finalize_bulk,
    get_all_meta,
    get_db_summary,
    get_meta,
    init_db,
    set_meta,
)


def test_schema_tables_and_indexes(tmp_db_path: Path) -> None:
    conn = init_db(tmp_db_path)
    try:
        tables = {
            r[0]
            for r in conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table'"
            ).fetchall()
        }
        expected = {
            "meta",
            "modules",
            "declarations",
            "edges",
            "metrics",
            "clusters",
            "symbols",
            "module_imports",
        }
        assert expected.issubset(tables)
        assert get_meta(conn, "schema_version") == SCHEMA_VERSION

        indexes = {
            r[0]
            for r in conn.execute(
                "SELECT name FROM sqlite_master WHERE type='index'"
            ).fetchall()
        }
        assert "idx_decl_canonical_hash" in indexes
        assert "idx_edges_src" in indexes
        assert "idx_edges_dst" in indexes
        assert "idx_metrics_bottleneck" in indexes
    finally:
        conn.close()


def test_bulk_insert_and_finalize_and_readonly(tmp_db_path: Path) -> None:
    conn = init_db(tmp_db_path, bulk=True, create_idx=False)
    try:
        batch_insert_modules(
            conn,
            [
                ("Main", "Main", 10, 0),
                ("Mathlib.Data.Nat", "Mathlib", 500, 1),
            ],
        )
        conn.commit()
        mod_map = {
            r["path"]: r["id"]
            for r in conn.execute("SELECT id, path FROM modules").fetchall()
        }
        batch_insert_declarations(
            conn,
            [
                (
                    "Main.foo",
                    "foo",
                    mod_map["Main"],
                    "theorem",
                    "True",
                    "h1",
                    4,
                    10,
                    "doc",
                    0,
                    0,
                    1,
                    4,
                    '["propext"]',
                ),
                (
                    "Nat.zero_le",
                    "zero_le",
                    mod_map["Mathlib.Data.Nat"],
                    "theorem",
                    "∀ n, 0 ≤ n",
                    "h2",
                    2,
                    5,
                    "",
                    1,
                    1,
                    1,
                    2,
                    None,
                ),
            ],
        )
        conn.commit()
        decl_map = {
            r["name"]: r["id"]
            for r in conn.execute("SELECT id, name FROM declarations").fetchall()
        }
        batch_insert_edges(conn, [(decl_map["Main.foo"], decl_map["Nat.zero_le"], "proof")])
        batch_insert_module_imports(
            conn, [(mod_map["Main"], "Mathlib.Data.Nat", mod_map["Mathlib.Data.Nat"])]
        )
        set_meta(conn, "custom_key", "custom_val")
        finalize_bulk(conn)

        summary = get_db_summary(conn)
        assert summary["modules"] == 2
        assert summary["project_modules"] == 1
        assert summary["mathlib_modules"] == 1
        assert summary["declarations"] == 2
        assert summary["edges"] == 1
        assert summary["module_imports"] == 1
        assert get_all_meta(conn)["custom_key"] == "custom_val"
    finally:
        conn.close()

    # Read-only connection should work and reject writes
    ro = connect_db(tmp_db_path, readonly=True)
    try:
        assert get_meta(ro, "custom_key") == "custom_val"
        with pytest.raises(sqlite3.OperationalError):
            ro.execute("INSERT INTO meta (key, value) VALUES ('x', 'y')")
    finally:
        ro.close()


def test_edge_kind_constraint(mem_db: sqlite3.Connection) -> None:
    with pytest.raises(sqlite3.IntegrityError):
        mem_db.execute("INSERT INTO edges (src_id, dst_id, kind) VALUES (1, 2, 'bogus')")
