"""Bridge importing JSONL output from the Lean 4 .olean kernel extractor into SQLite."""

from __future__ import annotations

import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from proof_compressor.ingest.lean_parser import (
    MATHLIB_ROOT_PACKAGES,
    canonical_type_hash,
    is_bookkeeping_decl,
)
from proof_compressor.schema import (
    finalize_bulk,
    init_db,
    set_meta,
)


@dataclass
class OleanIngestStats:
    jsonl_path: str
    records_read: int = 0
    modules_inserted: int = 0
    declarations_inserted: int = 0
    declarations_updated: int = 0
    boundary_stubs_inserted: int = 0
    edges_inserted: int = 0
    elapsed_seconds: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _infer_is_mathlib(name: str, module_path: str, explicit: bool | None) -> bool:
    if explicit is not None:
        return bool(explicit)
    root_mod = module_path.split(".", 1)[0] if module_path else ""
    if root_mod in MATHLIB_ROOT_PACKAGES:
        return True
    root_name = name.split(".", 1)[0] if name else ""
    return root_name in MATHLIB_ROOT_PACKAGES


def _normalize_kind(raw_kind: str | None) -> str:
    if not raw_kind:
        return "other"
    k = raw_kind.strip().lower()
    mapping = {
        "thm": "theorem",
        "theorem": "theorem",
        "lemma": "lemma",
        "defn": "def",
        "def": "def",
        "abbrev": "abbrev",
        "axiom": "axiom",
        "opaque": "opaque",
        "induct": "inductive",
        "inductive": "inductive",
        "ctor": "other",
        "rec": "other",
        "quot": "axiom",
        "structure": "structure",
        "class": "class",
        "instance": "instance",
        "constant": "constant",
    }
    return mapping.get(k, "other")


def ingest_olean_jsonl(
    jsonl_path: str | Path,
    db_path: str | Path,
    *,
    merge: bool = True,
    overwrite_types: bool = False,
    create_boundary_stubs: bool = True,
    batch_size: int = 5000,
) -> OleanIngestStats:
    """Import declarations and kernel dependency edges from ExtractDag JSONL into SQLite.

    Expected JSONL fields per line:
      - name (str, required): Fully qualified Lean constant name
      - module (str, optional): Dotted module path
      - kind (str, optional): theorem|lemma|def|axiom|inductive|opaque|...
      - type (str, optional): Pretty-printed type signature
      - proof_term_size (int, optional): Kernel Expr node count
      - is_mathlib (bool, optional): Whether constant belongs to Mathlib/Init/Std/Lean
      - axioms (list[str], optional): Kernel axiom footprint (`#print axioms`)
      - type_deps (list[str], optional): Constants appearing in type Expr
      - value_deps (list[str], optional): Constants appearing in value/proof Expr
      - deps (list[str], optional): General constant dependencies (emitted as kind='ref')
      - docstring (str, optional)
      - start_line / end_line / body_loc (int, optional)
    """
    t0 = time.monotonic()
    jpath = Path(jsonl_path)
    if not jpath.exists():
        raise FileNotFoundError(f"JSONL file not found: {jpath}")

    stats = OleanIngestStats(jsonl_path=str(jpath))
    conn = init_db(db_path, bulk=True, create_idx=False)

    try:
        mod_path_to_id: dict[str, int] = {}
        decl_name_to_id: dict[str, int] = {}

        if merge:
            for row in conn.execute("SELECT id, path FROM modules"):
                mod_path_to_id[row["path"]] = row["id"]
            for row in conn.execute("SELECT id, name FROM declarations"):
                decl_name_to_id[row["name"]] = row["id"]

        next_mod_id = (max(mod_path_to_id.values()) + 1) if mod_path_to_id else 1
        next_decl_id = (max(decl_name_to_id.values()) + 1) if decl_name_to_id else 1

        mod_batch: list[tuple[int, str, str, int, int]] = []
        decl_insert_batch: list[tuple[Any, ...]] = []
        decl_update_batch: list[tuple[Any, ...]] = []

        # Store raw edges until all declarations are loaded: (src_id, dst_name, edge_kind)
        pending_edges: list[tuple[int, str, str]] = []

        def _ensure_module(mod_path: str, is_mathlib: bool) -> int:
            nonlocal next_mod_id
            mpath = mod_path or ("Mathlib" if is_mathlib else "Unknown")
            mid = mod_path_to_id.get(mpath)
            if mid is not None:
                return mid
            mid = next_mod_id
            next_mod_id += 1
            pkg = mpath.split(".", 1)[0]
            mod_path_to_id[mpath] = mid
            mod_batch.append((mid, mpath, pkg, 0, int(is_mathlib)))
            stats.modules_inserted += 1
            return mid

        def _flush_decls() -> None:
            if mod_batch:
                conn.executemany(
                    "INSERT OR IGNORE INTO modules (id, path, package, loc, is_mathlib) "
                    "VALUES (?, ?, ?, ?, ?)",
                    mod_batch,
                )
                mod_batch.clear()
            if decl_insert_batch:
                conn.executemany(
                    "INSERT OR IGNORE INTO declarations ("
                    "id, name, short_name, module_id, kind, type_sig, canonical_type_hash, "
                    "body_loc, proof_term_size, docstring, is_mathlib, is_bookkeeping, "
                    "start_line, end_line, axioms_json"
                    ") VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                    decl_insert_batch,
                )
                decl_insert_batch.clear()
            if decl_update_batch:
                if overwrite_types:
                    conn.executemany(
                        "UPDATE declarations SET "
                        "proof_term_size = ?, axioms_json = ?, type_sig = ?, "
                        "canonical_type_hash = ?, kind = COALESCE(NULLIF(?, 'other'), kind) "
                        "WHERE id = ?",
                        decl_update_batch,
                    )
                else:
                    conn.executemany(
                        "UPDATE declarations SET "
                        "proof_term_size = ?, axioms_json = ?, "
                        "type_sig = COALESCE(NULLIF(type_sig, ''), ?), "
                        "canonical_type_hash = COALESCE(NULLIF(canonical_type_hash, ''), ?) "
                        "WHERE id = ?",
                        decl_update_batch,
                    )
                decl_update_batch.clear()
            conn.commit()

        with open(jpath, "r", encoding="utf-8") as fh:
            for raw_line in fh:
                line = raw_line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                name = rec.get("name")
                if not name:
                    continue
                stats.records_read += 1

                mod_path = rec.get("module") or ""
                is_mathlib = _infer_is_mathlib(name, mod_path, rec.get("is_mathlib"))
                kind = _normalize_kind(rec.get("kind"))
                type_sig = rec.get("type") or rec.get("type_sig") or ""
                c_hash = canonical_type_hash(type_sig) if type_sig else ""
                proof_size = int(rec.get("proof_term_size") or 0)
                axioms = rec.get("axioms")
                axioms_json = json.dumps(axioms) if axioms is not None else None
                docstring = rec.get("docstring")
                start_line = int(rec.get("start_line") or 0)
                end_line = int(rec.get("end_line") or 0)
                body_loc = int(
                    rec.get("body_loc")
                    or (max(1, end_line - start_line + 1) if end_line >= start_line > 0 else 0)
                )
                short_name = name.rsplit(".", 1)[-1]
                bk = is_bookkeeping_decl(kind, short_name, type_sig, "", body_loc)

                existing_id = decl_name_to_id.get(name)
                if existing_id is not None:
                    src_id = existing_id
                    if overwrite_types:
                        decl_update_batch.append(
                            (proof_size, axioms_json, type_sig, c_hash, kind, src_id)
                        )
                    else:
                        decl_update_batch.append(
                            (proof_size, axioms_json, type_sig, c_hash, src_id)
                        )
                    stats.declarations_updated += 1
                else:
                    mod_id = _ensure_module(mod_path, is_mathlib)
                    src_id = next_decl_id
                    next_decl_id += 1
                    decl_name_to_id[name] = src_id
                    decl_insert_batch.append(
                        (
                            src_id,
                            name,
                            short_name,
                            mod_id,
                            kind,
                            type_sig,
                            c_hash,
                            body_loc,
                            proof_size,
                            docstring,
                            int(is_mathlib),
                            int(bk),
                            start_line,
                            end_line,
                            axioms_json,
                        )
                    )
                    stats.declarations_inserted += 1

                for dep in rec.get("type_deps") or ():
                    if dep and dep != name:
                        pending_edges.append((src_id, dep, "type"))
                for dep in rec.get("value_deps") or ():
                    if dep and dep != name:
                        pending_edges.append((src_id, dep, "proof"))
                for dep in rec.get("deps") or ():
                    if dep and dep != name:
                        pending_edges.append((src_id, dep, "ref"))

                if len(decl_insert_batch) + len(decl_update_batch) >= batch_size:
                    _flush_decls()

        _flush_decls()

        # Pass 2: Insert edges (optionally creating Mathlib/external boundary stubs)
        edge_batch: list[tuple[int, int, str]] = []
        edge_flush_size = max(batch_size * 4, 20000)

        def _flush_edges() -> None:
            if mod_batch or decl_insert_batch:
                _flush_decls()
            if edge_batch:
                cur = conn.executemany(
                    "INSERT OR IGNORE INTO edges (src_id, dst_id, kind) VALUES (?, ?, ?)",
                    edge_batch,
                )
                stats.edges_inserted += max(0, cur.rowcount)
                edge_batch.clear()
                conn.commit()

        for src_id, dst_name, ekind in pending_edges:
            dst_id = decl_name_to_id.get(dst_name)
            if dst_id is None and create_boundary_stubs:
                root_pkg = dst_name.split(".", 1)[0] if "." in dst_name else "Mathlib"
                stub_mod_path = root_pkg if root_pkg in MATHLIB_ROOT_PACKAGES else "Mathlib"
                mod_id = _ensure_module(stub_mod_path, True)
                dst_id = next_decl_id
                next_decl_id += 1
                decl_name_to_id[dst_name] = dst_id
                decl_insert_batch.append(
                    (
                        dst_id,
                        dst_name,
                        dst_name.rsplit(".", 1)[-1],
                        mod_id,
                        "constant",
                        "",
                        "",
                        0,
                        0,
                        None,
                        1,
                        0,
                        0,
                        0,
                        None,
                    )
                )
                stats.boundary_stubs_inserted += 1

            if dst_id is not None and dst_id != src_id:
                edge_batch.append((src_id, dst_id, ekind))
                if len(edge_batch) >= edge_flush_size:
                    _flush_edges()

        _flush_edges()

        stats.elapsed_seconds = round(time.monotonic() - t0, 3)
        set_meta(conn, "olean_jsonl_path", str(jpath))
        set_meta(conn, "ingest_mode", "olean" if not merge else "hybrid")
        set_meta(conn, "olean_records", str(stats.records_read))
        set_meta(conn, "olean_edges", str(stats.edges_inserted))
        finalize_bulk(conn)
    finally:
        conn.close()

    return stats
