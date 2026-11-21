"""SQLite schema contract and bulk-insert helpers for proof-compressor."""

from __future__ import annotations

import sqlite3
from pathlib import Path
from typing import Any, Iterable, Sequence

SCHEMA_VERSION = "1"

VALID_EDGE_KINDS = ("type", "proof", "ref", "import")
VALID_DECL_KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "inductive",
    "instance",
    "axiom",
    "opaque",
    "constant",
    "other",
)

SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS meta (
    key TEXT PRIMARY KEY,
    value TEXT
);

CREATE TABLE IF NOT EXISTS modules (
    id INTEGER PRIMARY KEY,
    path TEXT UNIQUE,
    package TEXT,
    loc INTEGER DEFAULT 0,
    is_mathlib INTEGER DEFAULT 0
);

CREATE TABLE IF NOT EXISTS declarations (
    id INTEGER PRIMARY KEY,
    name TEXT UNIQUE,
    short_name TEXT,
    module_id INTEGER,
    kind TEXT,
    type_sig TEXT,
    canonical_type_hash TEXT,
    body_loc INTEGER DEFAULT 0,
    proof_term_size INTEGER DEFAULT 0,
    docstring TEXT,
    is_mathlib INTEGER DEFAULT 0,
    is_bookkeeping INTEGER DEFAULT 0,
    start_line INTEGER DEFAULT 0,
    end_line INTEGER DEFAULT 0,
    axioms_json TEXT
);

CREATE TABLE IF NOT EXISTS edges (
    src_id INTEGER NOT NULL,
    dst_id INTEGER NOT NULL,
    kind TEXT NOT NULL CHECK (kind IN ('type', 'proof', 'ref', 'import')),
    PRIMARY KEY (src_id, dst_id, kind)
);

CREATE TABLE IF NOT EXISTS metrics (
    decl_id INTEGER PRIMARY KEY,
    reachable INTEGER DEFAULT 0,
    in_degree INTEGER DEFAULT 0,
    out_degree INTEGER DEFAULT 0,
    scc_id INTEGER,
    dominator_depth INTEGER DEFAULT 0,
    bottleneck_score REAL DEFAULT 0.0,
    cluster_id INTEGER
);

CREATE TABLE IF NOT EXISTS clusters (
    id INTEGER PRIMARY KEY,
    parent_id INTEGER,
    level INTEGER DEFAULT 0,
    title TEXT,
    decl_count INTEGER DEFAULT 0,
    total_loc INTEGER DEFAULT 0,
    interface_in_json TEXT,
    interface_out_json TEXT,
    summary TEXT
);

CREATE TABLE IF NOT EXISTS symbols (
    decl_id INTEGER PRIMARY KEY,
    latex_macro TEXT,
    display_name TEXT,
    math_definition TEXT,
    centrality REAL DEFAULT 0.0
);

CREATE TABLE IF NOT EXISTS module_imports (
    src_module_id INTEGER NOT NULL,
    dst_module_path TEXT NOT NULL,
    dst_module_id INTEGER,
    PRIMARY KEY (src_module_id, dst_module_path)
);
"""

INDEXES_SQL = """
CREATE INDEX IF NOT EXISTS idx_modules_package ON modules(package);
CREATE INDEX IF NOT EXISTS idx_modules_mathlib ON modules(is_mathlib);

CREATE INDEX IF NOT EXISTS idx_decl_module ON declarations(module_id);
CREATE INDEX IF NOT EXISTS idx_decl_short_name ON declarations(short_name);
CREATE INDEX IF NOT EXISTS idx_decl_canonical_hash ON declarations(canonical_type_hash);
CREATE INDEX IF NOT EXISTS idx_decl_kind ON declarations(kind);
CREATE INDEX IF NOT EXISTS idx_decl_mathlib ON declarations(is_mathlib);
CREATE INDEX IF NOT EXISTS idx_decl_bookkeeping ON declarations(is_bookkeeping);

CREATE INDEX IF NOT EXISTS idx_edges_src ON edges(src_id);
CREATE INDEX IF NOT EXISTS idx_edges_dst ON edges(dst_id);
CREATE INDEX IF NOT EXISTS idx_edges_kind ON edges(kind);

CREATE INDEX IF NOT EXISTS idx_metrics_reachable ON metrics(reachable);
CREATE INDEX IF NOT EXISTS idx_metrics_cluster ON metrics(cluster_id);
CREATE INDEX IF NOT EXISTS idx_metrics_bottleneck ON metrics(bottleneck_score DESC);
CREATE INDEX IF NOT EXISTS idx_metrics_scc ON metrics(scc_id);

CREATE INDEX IF NOT EXISTS idx_clusters_parent ON clusters(parent_id);
CREATE INDEX IF NOT EXISTS idx_clusters_level ON clusters(level);

CREATE INDEX IF NOT EXISTS idx_mod_imports_src ON module_imports(src_module_id);
CREATE INDEX IF NOT EXISTS idx_mod_imports_dst ON module_imports(dst_module_id);
CREATE INDEX IF NOT EXISTS idx_mod_imports_path ON module_imports(dst_module_path);
"""


def _is_memory_path(db_path: str | Path) -> bool:
    s = str(db_path)
    return s == ":memory:" or s.startswith("file::memory:")


def connect_db(
    db_path: str | Path,
    *,
    bulk: bool = False,
    readonly: bool = False,
    timeout: float = 30.0,
) -> sqlite3.Connection:
    """Open a SQLite connection tuned for proof-compressor workloads."""
    is_mem = _is_memory_path(db_path)
    if not is_mem and not readonly:
        Path(db_path).parent.mkdir(parents=True, exist_ok=True)

    if readonly and not is_mem:
        uri = f"file:{Path(db_path).resolve()}?mode=ro"
        conn = sqlite3.connect(uri, uri=True, timeout=timeout)
    else:
        conn = sqlite3.connect(str(db_path), timeout=timeout)

    conn.row_factory = sqlite3.Row

    if readonly:
        conn.execute("PRAGMA query_only = ON")
        conn.execute("PRAGMA cache_size = -64000")
        conn.execute("PRAGMA temp_store = MEMORY")
        return conn

    if not is_mem:
        conn.execute("PRAGMA journal_mode = WAL")

    if bulk:
        conn.execute("PRAGMA synchronous = OFF")
        conn.execute("PRAGMA cache_size = -256000")
        conn.execute("PRAGMA temp_store = MEMORY")
        conn.execute("PRAGMA mmap_size = 268435456")
        if not is_mem:
            conn.execute("PRAGMA locking_mode = EXCLUSIVE")
    else:
        conn.execute("PRAGMA synchronous = NORMAL")
        conn.execute("PRAGMA cache_size = -64000")
        conn.execute("PRAGMA temp_store = MEMORY")

    conn.execute("PRAGMA foreign_keys = OFF")
    return conn


def init_db(
    db_path: str | Path,
    *,
    bulk: bool = False,
    create_idx: bool = True,
) -> sqlite3.Connection:
    """Create/open a database and initialize all schema tables (and optionally indexes)."""
    conn = connect_db(db_path, bulk=bulk)
    conn.executescript(SCHEMA_SQL)
    if create_idx:
        conn.executescript(INDEXES_SQL)
    set_meta(conn, "schema_version", SCHEMA_VERSION)
    conn.commit()
    return conn


def create_indexes(conn: sqlite3.Connection) -> None:
    """Create all schema indexes (idempotent). Call after bulk ingestion."""
    conn.executescript(INDEXES_SQL)
    conn.commit()


def finalize_bulk(conn: sqlite3.Connection) -> None:
    """Build indexes, restore normal durability/locking pragmas, and optimize."""
    create_indexes(conn)
    conn.execute("PRAGMA optimize")
    conn.execute("PRAGMA synchronous = NORMAL")
    conn.execute("PRAGMA locking_mode = NORMAL")
    conn.commit()


def set_meta(conn: sqlite3.Connection, key: str, value: str) -> None:
    """Upsert a key-value pair in the meta table."""
    conn.execute(
        "INSERT INTO meta (key, value) VALUES (?, ?) "
        "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (key, str(value)),
    )


def get_meta(
    conn: sqlite3.Connection,
    key: str,
    default: str | None = None,
) -> str | None:
    """Read a metadata value by key."""
    row = conn.execute("SELECT value FROM meta WHERE key = ?", (key,)).fetchone()
    return row["value"] if row is not None else default


def get_all_meta(conn: sqlite3.Connection) -> dict[str, str]:
    """Return all key-value pairs from the meta table."""
    rows = conn.execute("SELECT key, value FROM meta").fetchall()
    return {r["key"]: r["value"] for r in rows}


def batch_insert_modules(
    conn: sqlite3.Connection,
    rows: Iterable[Sequence[Any]],
) -> int:
    """Bulk-insert module tuples: (path, package, loc, is_mathlib)."""
    cur = conn.executemany(
        "INSERT OR IGNORE INTO modules (path, package, loc, is_mathlib) "
        "VALUES (?, ?, ?, ?)",
        rows,
    )
    return cur.rowcount


def batch_insert_declarations(
    conn: sqlite3.Connection,
    rows: Iterable[Sequence[Any]],
) -> int:
    """Bulk-insert declaration tuples matching the declarations column order (excluding id)."""
    cur = conn.executemany(
        "INSERT OR IGNORE INTO declarations ("
        "name, short_name, module_id, kind, type_sig, canonical_type_hash, "
        "body_loc, proof_term_size, docstring, is_mathlib, is_bookkeeping, "
        "start_line, end_line, axioms_json"
        ") VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
        rows,
    )
    return cur.rowcount


def batch_insert_edges(
    conn: sqlite3.Connection,
    rows: Iterable[Sequence[Any]],
) -> int:
    """Bulk-insert edge tuples: (src_id, dst_id, kind)."""
    cur = conn.executemany(
        "INSERT OR IGNORE INTO edges (src_id, dst_id, kind) VALUES (?, ?, ?)",
        rows,
    )
    return cur.rowcount


def batch_insert_module_imports(
    conn: sqlite3.Connection,
    rows: Iterable[Sequence[Any]],
) -> int:
    """Bulk-insert module import tuples: (src_module_id, dst_module_path, dst_module_id)."""
    cur = conn.executemany(
        "INSERT OR IGNORE INTO module_imports (src_module_id, dst_module_path, dst_module_id) "
        "VALUES (?, ?, ?)",
        rows,
    )
    return cur.rowcount


def get_db_summary(conn: sqlite3.Connection) -> dict[str, Any]:
    """Return high-level counts and LOC statistics from the database."""
    mod_row = conn.execute(
        "SELECT COUNT(*) AS cnt, "
        "COALESCE(SUM(loc), 0) AS total_loc, "
        "COALESCE(SUM(CASE WHEN is_mathlib = 1 THEN 1 ELSE 0 END), 0) AS mathlib_mods "
        "FROM modules"
    ).fetchone()
    decl_row = conn.execute(
        "SELECT COUNT(*) AS cnt, "
        "COALESCE(SUM(body_loc), 0) AS total_body_loc, "
        "COALESCE(SUM(CASE WHEN is_mathlib = 1 THEN 1 ELSE 0 END), 0) AS mathlib_decls, "
        "COALESCE(SUM(CASE WHEN is_bookkeeping = 1 THEN 1 ELSE 0 END), 0) AS bookkeeping_decls "
        "FROM declarations"
    ).fetchone()
    edge_cnt = conn.execute("SELECT COUNT(*) FROM edges").fetchone()[0]
    mod_imp_cnt = conn.execute("SELECT COUNT(*) FROM module_imports").fetchone()[0]
    reach_cnt = conn.execute(
        "SELECT COUNT(*) FROM metrics WHERE reachable = 1"
    ).fetchone()[0]
    cluster_cnt = conn.execute("SELECT COUNT(*) FROM clusters").fetchone()[0]
    symbol_cnt = conn.execute("SELECT COUNT(*) FROM symbols").fetchone()[0]

    return {
        "modules": mod_row["cnt"],
        "mathlib_modules": mod_row["mathlib_mods"],
        "project_modules": mod_row["cnt"] - mod_row["mathlib_mods"],
        "total_loc": mod_row["total_loc"],
        "declarations": decl_row["cnt"],
        "mathlib_declarations": decl_row["mathlib_decls"],
        "project_declarations": decl_row["cnt"] - decl_row["mathlib_decls"],
        "bookkeeping_declarations": decl_row["bookkeeping_decls"],
        "total_body_loc": decl_row["total_body_loc"],
        "edges": edge_cnt,
        "module_imports": mod_imp_cnt,
        "reachable_declarations": reach_cnt,
        "clusters": cluster_cnt,
        "symbols": symbol_cnt,
    }
