"""Internal SQLite helpers shared across expose and refactor modules."""

from __future__ import annotations

import json
import sqlite3
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator

from proof_compressor.schema import connect_db

DbHandle = sqlite3.Connection | str | Path


@contextmanager
def open_db(db: DbHandle, *, readonly: bool = False) -> Iterator[sqlite3.Connection]:
    """Yield a sqlite3.Connection, closing it only if we opened it."""
    if isinstance(db, sqlite3.Connection):
        yield db
        return
    conn = connect_db(db, readonly=readonly)
    try:
        yield conn
    finally:
        conn.close()


def query_all(
    conn: sqlite3.Connection,
    sql: str,
    params: tuple[Any, ...] | list[Any] = (),
) -> list[dict[str, Any]]:
    """Execute a SELECT and return rows as plain dicts without mutating conn.row_factory."""
    cur = conn.cursor()
    cur.row_factory = sqlite3.Row
    cur.execute(sql, params)
    return [dict(r) for r in cur.fetchall()]


def query_one(
    conn: sqlite3.Connection,
    sql: str,
    params: tuple[Any, ...] | list[Any] = (),
) -> dict[str, Any] | None:
    """Execute a SELECT and return a single row as a dict, or None."""
    cur = conn.cursor()
    cur.row_factory = sqlite3.Row
    cur.execute(sql, params)
    row = cur.fetchone()
    return dict(row) if row is not None else None


def safe_json_loads(raw: str | None, default: Any) -> Any:
    """Parse JSON defensively, returning default on None or malformed JSON."""
    if not raw:
        return default
    try:
        return json.loads(raw)
    except (TypeError, ValueError):
        return default


def has_reachable_metrics(conn: sqlite3.Connection) -> bool:
    """Return True if the metrics table contains at least one reachable declaration."""
    row = query_one(conn, "SELECT 1 AS ok FROM metrics WHERE reachable = 1 LIMIT 1")
    return row is not None


def get_meta_dict(conn: sqlite3.Connection) -> dict[str, str]:
    """Return all key-value pairs from the meta table."""
    rows = query_all(conn, "SELECT key, value FROM meta")
    return {r["key"]: r["value"] for r in rows}


def get_root_declaration_names(conn: sqlite3.Connection) -> list[str]:
    """Retrieve root theorem names from meta or infer highest-level sinks."""
    meta = get_meta_dict(conn)
    for key in ("analysis_roots", "root_theorems", "roots", "root_decls", "root_names"):
        val = meta.get(key)
        if val:
            parsed = safe_json_loads(val, None)
            if isinstance(parsed, list) and parsed:
                out: list[str] = []
                for item in parsed:
                    if isinstance(item, dict) and item.get("name"):
                        out.append(str(item["name"]))
                    elif item:
                        out.append(str(item))
                if out:
                    return out
            if isinstance(val, str):
                parts = [p.strip() for p in val.split(",") if p.strip()]
                if parts:
                    return parts

    # Fallback: reachable theorems/lemmas with in_degree = 0 and high out_degree
    if has_reachable_metrics(conn):
        rows = query_all(
            conn,
            """
            SELECT d.name
            FROM declarations d
            JOIN metrics m ON m.decl_id = d.id
            WHERE m.reachable = 1
              AND d.is_mathlib = 0
              AND m.in_degree = 0
              AND d.kind IN ('theorem', 'lemma')
            ORDER BY m.bottleneck_score DESC, m.out_degree DESC, d.body_loc DESC
            LIMIT 10
            """,
        )
        if rows:
            return [r["name"] for r in rows]

    # Ultimate fallback: non-mathlib theorems with no incoming edges
    rows = query_all(
        conn,
        """
        SELECT d.name
        FROM declarations d
        WHERE d.is_mathlib = 0
          AND d.kind IN ('theorem', 'lemma')
          AND NOT EXISTS (SELECT 1 FROM edges e WHERE e.dst_id = d.id)
        ORDER BY d.body_loc DESC
        LIMIT 10
        """,
    )
    return [r["name"] for r in rows]


def get_cluster_hierarchy(
    conn: sqlite3.Connection,
) -> tuple[list[dict[str, Any]], dict[int, list[dict[str, Any]]], dict[int, int]]:
    """Load clusters and build (chapters, sections_by_chapter, cluster_to_chapter).

    Handles both 2-level hierarchy (level=0 chapters, level=1 sections where
    metrics.cluster_id points to level=1) and flat single-level clusters.
    """
    all_clusters = query_all(
        conn,
        """
        SELECT id, parent_id, level, title, decl_count, total_loc,
               interface_in_json, interface_out_json, summary
        FROM clusters
        ORDER BY level ASC, id ASC
        """,
    )
    chapters: list[dict[str, Any]] = []
    sections_by_chapter: dict[int, list[dict[str, Any]]] = {}
    cluster_to_chapter: dict[int, int] = {}

    if not all_clusters:
        return chapters, sections_by_chapter, cluster_to_chapter

    # Chapters are rows with parent_id IS NULL (or level == 0)
    chapter_rows = [c for c in all_clusters if c["parent_id"] is None]
    if not chapter_rows:
        chapter_rows = all_clusters

    chapter_ids = {int(c["id"]) for c in chapter_rows}
    for c in chapter_rows:
        cid = int(c["id"])
        chapters.append(c)
        sections_by_chapter[cid] = []
        cluster_to_chapter[cid] = cid

    for c in all_clusters:
        cid = int(c["id"])
        pid = c["parent_id"]
        if pid is not None:
            pid_int = int(pid)
            if pid_int in chapter_ids:
                sections_by_chapter[pid_int].append(c)
                cluster_to_chapter[cid] = pid_int
            else:
                cluster_to_chapter[cid] = cid

    return chapters, sections_by_chapter, cluster_to_chapter

