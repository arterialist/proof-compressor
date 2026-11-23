"""Zero-extraction streaming ingestor for multi-part tar.gz archives and Lean 4 source trees."""

from __future__ import annotations

import array
import glob
import gzip
import io
import json
import os
import re
import tarfile
import tempfile
import time
from collections import OrderedDict, deque
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Iterator, Sequence

from proof_compressor.ingest.lean_parser import (
    MATHLIB_ROOT_PACKAGES,
    normalize_module_path,
    parse_lean_source,
)
from proof_compressor.schema import (
    finalize_bulk,
    init_db,
    set_meta,
)

_PART_FILE_RE = re.compile(r"^(.*\.tar(?:\.gz)?\.part)(\d+)$")
_PROJECTION_SUFFIXES = frozenset({
    "mp", "mpr", "symm", "trans", "left", "right", "elim", "intro",
    "val", "prop", "toFun", "mk", "rfl", "ne", "le", "lt", "ge", "gt",
    "not", "1", "2", "fst", "snd", "of_eq", "eq",
})
_MAX_AMBIGUOUS_SHORT_CANDS = 64
_BIT_MASKS = (1, 2, 4, 8, 16, 32, 64, 128)


@dataclass
class IngestStats:
    source: str
    files_seen: int = 0
    files_ingested: int = 0
    files_skipped: int = 0
    modules_inserted: int = 0
    declarations_inserted: int = 0
    module_imports_inserted: int = 0
    edges_inserted: int = 0
    total_loc: int = 0
    pass1_seconds: float = 0.0
    pass2_seconds: float = 0.0
    total_seconds: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


class ConcatenatedFileReader(io.RawIOBase):
    """Streaming RawIOBase that concatenates ordered file parts with zero copying."""

    def __init__(self, paths: Sequence[Path]) -> None:
        super().__init__()
        self._paths = [Path(p) for p in paths]
        self._idx = 0
        self._fh = open(self._paths[0], "rb") if self._paths else None
        self.bytes_read = 0

    def readable(self) -> bool:
        return True

    def readinto(self, b: bytearray | memoryview) -> int:  # type: ignore[override]
        if self._fh is None:
            return 0
        n = self._fh.readinto(b)
        while n == 0:
            self._fh.close()
            self._idx += 1
            if self._idx >= len(self._paths):
                self._fh = None
                return 0
            self._fh = open(self._paths[self._idx], "rb")
            n = self._fh.readinto(b)
        self.bytes_read += n
        return n

    def close(self) -> None:
        if self._fh is not None:
            try:
                self._fh.close()
            finally:
                self._fh = None
        super().close()


def _natural_part_key(p: Path) -> tuple[str, int, str]:
    m = _PART_FILE_RE.match(p.name)
    if m:
        return (m.group(1), int(m.group(2)), p.name)
    return (p.name, 0, p.name)


def resolve_input_source(
    source: str | Path | Sequence[str | Path],
) -> tuple[str, list[Path]]:
    """Classify input source as ('archive', [part_paths]), ('dir', [dir_path]), or ('files', [lean_paths])."""
    if not isinstance(source, (str, os.PathLike)):
        paths = [Path(p) for p in source]
        if not paths:
            raise FileNotFoundError("Empty input source sequence")
        if all(p.suffix == ".lean" for p in paths):
            return ("files", paths)
        return ("archive", paths)

    src_str = os.fspath(source)

    if any(ch in src_str for ch in ("*", "?", "[")):
        matched = sorted((Path(p) for p in glob.glob(src_str)), key=_natural_part_key)
        if not matched:
            raise FileNotFoundError(f"No files matched glob pattern: {src_str}")
        if all(p.suffix == ".lean" for p in matched):
            return ("files", matched)
        return ("archive", matched)

    p = Path(src_str)
    if not p.exists():
        raise FileNotFoundError(f"Input source does not exist: {p}")

    if p.is_dir():
        part_files = sorted(
            (c for c in p.iterdir() if c.is_file() and _PART_FILE_RE.match(c.name)),
            key=_natural_part_key,
        )
        if part_files:
            has_lean = any(p.rglob("*.lean"))
            if not has_lean:
                return ("archive", part_files)
        return ("dir", [p])

    if p.suffix == ".lean":
        return ("files", [p])

    m = _PART_FILE_RE.match(p.name)
    if m:
        prefix = m.group(1)
        siblings = sorted(
            (
                c
                for c in p.parent.iterdir()
                if c.is_file()
                and c.name.startswith(prefix)
                and _PART_FILE_RE.match(c.name)
            ),
            key=_natural_part_key,
        )
        if siblings:
            return ("archive", siblings)

    return ("archive", [p])


def iter_lean_sources(
    source: str | Path | Sequence[str | Path],
) -> Iterator[tuple[str, str]]:
    """Stream (relative_path, utf8_text) for every .lean file in an archive, parts, or directory."""
    kind, paths = resolve_input_source(source)

    if kind == "files":
        # Paths relative to the inputs' common directory: `RH/A/Basic.lean` and
        # `RH/B/Basic.lean` must not both collapse to module `Basic`.
        base = Path(os.path.commonpath([str(p.resolve().parent) for p in paths]))
        for p in paths:
            rel = p.resolve().relative_to(base).as_posix()
            yield (rel, p.read_text(encoding="utf-8", errors="replace"))
        return

    if kind == "dir":
        root = paths[0]
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames.sort()
            dirnames[:] = [
                d for d in dirnames if d not in (".git", ".venv", "__pycache__", "build")
            ]
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    full = Path(dirpath) / fn
                    rel = full.relative_to(root).as_posix()
                    try:
                        text = full.read_text(encoding="utf-8", errors="replace")
                    except OSError:
                        continue
                    yield (rel, text)
        return

    raw_reader = ConcatenatedFileReader(paths)
    buf_reader = io.BufferedReader(raw_reader, buffer_size=4 * 1024 * 1024)
    gz_file: gzip.GzipFile | None = None
    try:
        magic = buf_reader.peek(2)[:2]
        if magic == b"\x1f\x8b":
            gz_file = gzip.GzipFile(fileobj=buf_reader, mode="rb")
            stream: io.BufferedIOBase | gzip.GzipFile = gz_file
        else:
            stream = buf_reader

        with tarfile.open(fileobj=stream, mode="r|", bufsize=1024 * 1024) as tf:
            for member in tf:
                if not member.isfile():
                    continue
                if not member.name.endswith(".lean"):
                    continue
                ef = tf.extractfile(member)
                if ef is None:
                    continue
                raw_bytes = ef.read()
                yield (member.name, raw_bytes.decode("utf-8", errors="replace"))
    finally:
        if gz_file is not None:
            gz_file.close()
        buf_reader.close()
        raw_reader.close()


class TransitiveImportIndex:
    """Fast, zero-allocation transitive module import index with topological bit-packing and hub pinning.

    Assigns each module a topological bit position `topo_bit[mod_id]` (leaves get low bits,
    roots get high bits), so foundation bitsets are only a few hundred bytes. Uses C-level
    Python `int` bitwise-OR to compute exact closures, pins high-in-degree hub modules to
    prevent cache thrashing, and converts only the active module's bitset to `bytes` once
    for O(1) zero-allocation membership checks.
    """

    def __init__(
        self,
        num_mods: int,
        direct_imports: dict[int, list[int]],
        *,
        max_pinned_hubs: int = 12000,
        max_lru_entries: int = 4096,
    ) -> None:
        self._direct = direct_imports
        self._max_lru = max_lru_entries
        self._pinned: dict[int, int] = {}
        self._lru: OrderedDict[int, int] = OrderedDict()

        # Compute importer counts (how many modules directly import m) + Kahn topological order
        # Edge direction: `src` imports `dep`, so `dep` must precede `src` in topo order.
        out_dep_count = array.array("I", [0] * (num_mods + 1))
        importers: list[list[int]] = [[] for _ in range(num_mods + 1)]
        importer_cnt = array.array("I", [0] * (num_mods + 1))

        for src, deps in direct_imports.items():
            out_dep_count[src] = len(deps)
            for dep in deps:
                importers[dep].append(src)
                importer_cnt[dep] += 1

        # Kahn's algorithm from leaf modules (0 imports) up to roots
        q: deque[int] = deque()
        for m in range(1, num_mods + 1):
            if out_dep_count[m] == 0:
                q.append(m)

        topo_bit = array.array("I", [0] * (num_mods + 1))
        next_bit = 0
        while q:
            m = q.popleft()
            topo_bit[m] = next_bit
            next_bit += 1
            for parent in importers[m]:
                rem = out_dep_count[parent] - 1
                out_dep_count[parent] = rem
                if rem == 0:
                    q.append(parent)

        # Assign remaining indices if any cycle existed
        self.has_cycles = next_bit < num_mods
        if self.has_cycles:
            for m in range(1, num_mods + 1):
                if out_dep_count[m] > 0:
                    topo_bit[m] = next_bit
                    next_bit += 1

        self.topo_bit = topo_bit

        # Identify high-fan-in hub modules (with non-empty imports) to pin permanently in cache
        hub_candidates = [
            (importer_cnt[m], m)
            for m in range(1, num_mods + 1)
            if importer_cnt[m] >= 2 and m in direct_imports
        ]
        if len(hub_candidates) > max_pinned_hubs:
            hub_candidates.sort(reverse=True)
            hub_candidates = hub_candidates[:max_pinned_hubs]
        self._hub_set: set[int] = {m for _, m in hub_candidates}

    def _get_int_bitset(self, mod_id: int) -> int:
        cached = self._pinned.get(mod_id)
        if cached is not None:
            return cached
        cached = self._lru.get(mod_id)
        if cached is not None:
            self._lru.move_to_end(mod_id)
            return cached

        deps = self._direct.get(mod_id)
        if not deps:
            bits = 1 << self.topo_bit[mod_id]
            return bits

        # Iterative post-order DFS (safe for arbitrary import depth)
        stack: list[tuple[int, bool]] = [(mod_id, False)]
        in_progress: set[int] = set()
        local_bits: dict[int, int] = {}
        topo_bit = self.topo_bit
        pinned = self._pinned
        lru = self._lru
        direct = self._direct

        while stack:
            node, expanded = stack.pop()
            if node in pinned or node in lru or node in local_bits:
                continue
            if not expanded:
                if node in in_progress:
                    local_bits[node] = 1 << topo_bit[node]
                    continue
                in_progress.add(node)
                stack.append((node, True))
                for dep in direct.get(node, ()):
                    if dep in pinned or dep in local_bits or dep in in_progress:
                        continue
                    cached_dep = lru.get(dep)
                    if cached_dep is not None:
                        # Snapshot now: computing a sibling subtree can evict it from the
                        # LRU before this node is finished, which would drop its closure.
                        local_bits[dep] = cached_dep
                        continue
                    stack.append((dep, False))
            else:
                in_progress.discard(node)
                bits = 1 << topo_bit[node]
                for dep in direct.get(node, ()):
                    db = pinned.get(dep)
                    if db is None:
                        db = local_bits.get(dep)
                    if db is None:
                        db = lru.get(dep)
                    if db is None:
                        db = 1 << topo_bit[dep]
                    bits |= db
                local_bits[node] = bits
                self._store(node, bits)

        return (
            pinned.get(mod_id)
            or lru.get(mod_id)
            or local_bits.get(mod_id)
            or (1 << topo_bit[mod_id])
        )

    def _store(self, mod_id: int, bits: int) -> None:
        if mod_id in self._hub_set:
            self._pinned[mod_id] = bits
            return
        self._lru[mod_id] = bits
        self._lru.move_to_end(mod_id)
        if len(self._lru) > self._max_lru:
            self._lru.popitem(last=False)

    def get_bytes_bitset(self, mod_id: int) -> bytes:
        """Return little-endian bytes bitset indexed by `self.topo_bit[cand_mod]`."""
        bits = self._get_int_bitset(mod_id)
        nbytes = (bits.bit_length() + 7) >> 3
        return bits.to_bytes(nbytes, "little")


def _add_index_entry(index: dict[str, int | list[int]], key: str, val: int) -> None:
    existing = index.get(key)
    if existing is None:
        index[key] = val
    elif isinstance(existing, int):
        index[key] = [existing, val]
    else:
        existing.append(val)


def ingest_source(
    source: str | Path | Sequence[str | Path],
    db_path: str | Path,
    *,
    max_files: int | None = None,
    path_filter: str | None = None,
    include_mathlib: bool = False,
    strip_prefixes: Sequence[str] = (),
    batch_size: int = 5000,
    progress_cb: Callable[[dict[str, Any]], None] | None = None,
    progress_every: int = 5000,
) -> IngestStats:
    """Stream Lean 4 source files from archive/parts/dir directly into SQLite in two passes.

    Pass 1 streams the archive ONCE with zero disk extraction, inserting modules,
    module_imports, and declarations while spilling compact per-module reference lists
    to a temporary gzipped file (automatically unlinked on close).

    Pass 2 resolves identifier references against exact transitive module import closures
    and namespace/open scopes into the `edges` table, then builds all SQLite indexes.
    """
    t0 = time.monotonic()
    src_desc = (
        ", ".join(str(p) for p in source)
        if not isinstance(source, (str, os.PathLike))
        else str(source)
    )
    stats = IngestStats(source=src_desc)
    filter_re = re.compile(path_filter) if path_filter else None

    conn = init_db(db_path, bulk=True, create_idx=False)

    # Name resolution state below starts empty, so ingesting on top of existing rows would
    # silently drop colliding modules/declarations while still writing edges for them.
    existing_mods = conn.execute("SELECT COUNT(*) FROM modules").fetchone()[0]
    if existing_mods:
        conn.close()
        raise ValueError(
            f"{db_path} already contains {existing_mods} modules; ingest into a fresh "
            "database (delete it first, or pass --skip-ingest to reuse it)."
        )

    next_mod_id = (conn.execute("SELECT COALESCE(MAX(id), 0) FROM modules").fetchone()[0]) + 1
    next_decl_id = (
        conn.execute("SELECT COALESCE(MAX(id), 0) FROM declarations").fetchone()[0]
    ) + 1

    mod_path_to_id: dict[str, int] = {}
    full_name_to_ids: dict[str, int | list[int]] = {}
    short_name_to_ids: dict[str, int | list[int]] = {}
    used_db_names: set[str] = set()

    decl_mod = array.array("I", [0] * next_decl_id)
    decl_line = array.array("I", [0] * next_decl_id)
    decl_full_names: list[str] = [""] * next_decl_id
    decl_short_names: list[str] = [""] * next_decl_id

    raw_mod_imports: dict[int, list[str]] = {}
    mod_decl_ids: dict[int, list[int]] = {}

    mod_batch: list[tuple[int, str, str, int, int]] = []
    imp_batch: list[tuple[int, str, int | None]] = []
    decl_batch: list[tuple[Any, ...]] = []

    def _flush_pass1() -> None:
        if mod_batch:
            conn.executemany(
                "INSERT OR IGNORE INTO modules (id, path, package, loc, is_mathlib) "
                "VALUES (?, ?, ?, ?, ?)",
                mod_batch,
            )
            mod_batch.clear()
        if imp_batch:
            conn.executemany(
                "INSERT OR IGNORE INTO module_imports (src_module_id, dst_module_path, dst_module_id) "
                "VALUES (?, ?, ?)",
                imp_batch,
            )
            imp_batch.clear()
        if decl_batch:
            conn.executemany(
                "INSERT OR IGNORE INTO declarations ("
                "id, name, short_name, module_id, kind, type_sig, canonical_type_hash, "
                "body_loc, proof_term_size, docstring, is_mathlib, is_bookkeeping, "
                "start_line, end_line, axioms_json"
                ") VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                decl_batch,
            )
            decl_batch.clear()
        conn.commit()

    spill_raw = tempfile.TemporaryFile(mode="w+b")
    try:
        with gzip.GzipFile(fileobj=spill_raw, mode="wb", compresslevel=1) as spill_gz:
            for raw_path, text in iter_lean_sources(source):
                stats.files_seen += 1
                mod_path, package, is_mathlib = normalize_module_path(
                    raw_path, strip_prefixes=strip_prefixes
                )

                if is_mathlib and not include_mathlib:
                    stats.files_skipped += 1
                    continue

                if filter_re and not (filter_re.search(mod_path) or filter_re.search(raw_path)):
                    stats.files_skipped += 1
                    continue

                if mod_path in mod_path_to_id:
                    stats.files_skipped += 1
                    continue

                parsed = parse_lean_source(
                    text, mod_path, package=package, is_mathlib=is_mathlib
                )

                mod_id = next_mod_id
                next_mod_id += 1
                mod_path_to_id[mod_path] = mod_id
                mod_batch.append(
                    (mod_id, parsed.path, parsed.package, parsed.loc, int(parsed.is_mathlib))
                )
                stats.files_ingested += 1
                stats.modules_inserted += 1
                stats.total_loc += parsed.loc

                if parsed.imports:
                    raw_mod_imports[mod_id] = parsed.imports
                    for imp in parsed.imports:
                        imp_batch.append((mod_id, imp, None))
                        stats.module_imports_inserted += 1

                mod_ref_records: list[list[Any]] = []
                m_dids: list[int] = []
                for d in parsed.declarations:
                    decl_id = next_decl_id
                    next_decl_id += 1

                    db_name = d.name
                    if db_name in used_db_names:
                        db_name = f"{mod_path}::{d.name}"
                        suffix_idx = 2
                        while db_name in used_db_names:
                            db_name = f"{mod_path}::{d.name}#{suffix_idx}"
                            suffix_idx += 1
                    used_db_names.add(db_name)

                    decl_batch.append(
                        (
                            decl_id,
                            db_name,
                            d.short_name,
                            mod_id,
                            d.kind,
                            d.type_sig,
                            d.canonical_type_hash,
                            d.body_loc,
                            0,
                            d.docstring,
                            int(parsed.is_mathlib),
                            int(d.is_bookkeeping),
                            d.start_line,
                            d.end_line,
                            None,
                        )
                    )
                    stats.declarations_inserted += 1

                    decl_mod.append(mod_id)
                    decl_line.append(d.start_line)
                    decl_full_names.append(d.name)
                    decl_short_names.append(d.short_name)
                    m_dids.append(decl_id)

                    _add_index_entry(full_name_to_ids, d.name, decl_id)
                    _add_index_entry(short_name_to_ids, d.short_name, decl_id)

                    if d.type_refs or d.proof_refs:
                        mod_ref_records.append(
                            [
                                decl_id,
                                list(d.namespace_stack),
                                list(d.open_namespaces),
                                d.type_refs,
                                d.proof_refs,
                            ]
                        )

                if m_dids:
                    mod_decl_ids[mod_id] = m_dids

                if mod_ref_records:
                    line_bytes = (
                        json.dumps([mod_id, mod_ref_records], separators=(",", ":")) + "\n"
                    ).encode("utf-8")
                    spill_gz.write(line_bytes)

                if len(decl_batch) >= batch_size or len(mod_batch) >= batch_size:
                    _flush_pass1()

                if progress_cb and stats.files_ingested % progress_every == 0:
                    progress_cb(
                        {
                            "phase": "pass1",
                            "files_ingested": stats.files_ingested,
                            "declarations": stats.declarations_inserted,
                            "elapsed_s": round(time.monotonic() - t0, 2),
                        }
                    )

                if max_files is not None and stats.files_ingested >= max_files:
                    break

            _flush_pass1()

        t_p1 = time.monotonic()
        stats.pass1_seconds = round(t_p1 - t0, 3)

        used_db_names.clear()

        # -------------------------------------------------------------------
        # Pass 2: Resolve module_imports.dst_module_id + declaration edges
        # -------------------------------------------------------------------
        direct_imports: dict[int, list[int]] = {}
        direct_import_sets: dict[int, set[int]] = {}
        has_missing_project_imp: set[int] = set()
        imp_updates: list[tuple[int, int, str]] = []

        for src_mod_id, imp_paths in raw_mod_imports.items():
            resolved_list: list[int] = []
            for imp_path in imp_paths:
                dst_mod_id = mod_path_to_id.get(imp_path)
                if dst_mod_id is not None:
                    resolved_list.append(dst_mod_id)
                    imp_updates.append((dst_mod_id, src_mod_id, imp_path))
                else:
                    root_pkg = imp_path.split(".", 1)[0]
                    if root_pkg not in MATHLIB_ROOT_PACKAGES:
                        has_missing_project_imp.add(src_mod_id)
            if resolved_list:
                direct_imports[src_mod_id] = resolved_list
                direct_import_sets[src_mod_id] = set(resolved_list)

        if imp_updates:
            conn.executemany(
                "UPDATE module_imports SET dst_module_id = ? "
                "WHERE src_module_id = ? AND dst_module_path = ?",
                imp_updates,
            )
            conn.commit()
            imp_updates.clear()
        raw_mod_imports.clear()

        num_mods = next_mod_id - 1
        import_index = TransitiveImportIndex(
            num_mods,
            direct_imports,
            max_pinned_hubs=12000,
            max_lru_entries=4096,
        )
        topo_bit = import_index.topo_bit
        has_cycles = import_index.has_cycles

        edge_batch: list[tuple[int, int, str]] = []
        edge_flush_size = max(batch_size * 4, 20000)

        def _flush_edges() -> None:
            if edge_batch:
                cur = conn.executemany(
                    "INSERT OR IGNORE INTO edges (src_id, dst_id, kind) VALUES (?, ?, ?)",
                    edge_batch,
                )
                stats.edges_inserted += max(0, cur.rowcount)
                edge_batch.clear()
                conn.commit()

        # Rewind spill file and resolve edges module-by-module
        spill_raw.seek(0)
        mods_resolved = 0

        # Active per-module state (lazy transitive bitset!)
        cur_mod_id = 0
        cur_mod_tbit = 0
        cur_direct_set: set[int] = set()
        cur_bytes: bytes | None = None
        cur_bytes_len = 0
        cur_has_trans_deps = False

        def _is_mod_reachable(cmod: int) -> bool:
            nonlocal cur_bytes, cur_bytes_len
            if cmod == cur_mod_id or cmod in cur_direct_set:
                return True
            if not cur_has_trans_deps:
                return False
            ct = topo_bit[cmod]
            if not has_cycles and ct >= cur_mod_tbit:
                return False
            if cur_bytes is None:
                cur_bytes = import_index.get_bytes_bitset(cur_mod_id)
                cur_bytes_len = len(cur_bytes)
            byte_i = ct >> 3
            return byte_i < cur_bytes_len and bool(cur_bytes[byte_i] & _BIT_MASKS[ct & 7])

        def _pick_best(
            cands: int | list[int],
            src_id: int,
            ns_prefixes: list[str],
            open_list: list[str],
            allow_unreached_exact: bool,
        ) -> int | None:
            if isinstance(cands, int):
                if cands == src_id:
                    return None
                if _is_mod_reachable(decl_mod[cands]):
                    return cands
                return cands if allow_unreached_exact else None

            # Multiple candidates: fast-path same-module & direct-import check
            n_cands = len(cands)
            if n_cands > _MAX_AMBIGUOUS_SHORT_CANDS:
                return None

            same_mod_best: int | None = None
            same_mod_best_ln = -1
            same_mod_any: int | None = None
            src_ln = decl_line[src_id]
            dir_cands: list[int] = []
            trans_cands: list[int] = []

            for cid in cands:
                if cid == src_id:
                    continue
                cmod = decl_mod[cid]
                if cmod == cur_mod_id:
                    ln = decl_line[cid]
                    if ln < src_ln and ln > same_mod_best_ln:
                        same_mod_best = cid
                        same_mod_best_ln = ln
                    elif same_mod_any is None:
                        same_mod_any = cid
                elif cmod in cur_direct_set:
                    dir_cands.append(cid)
                elif same_mod_best is None and same_mod_any is None and not dir_cands:
                    if _is_mod_reachable(cmod):
                        trans_cands.append(cid)

            if same_mod_best is not None:
                return same_mod_best
            if same_mod_any is not None:
                return same_mod_any

            if dir_cands:
                if len(dir_cands) == 1:
                    return dir_cands[0]
                pool = dir_cands
            elif trans_cands:
                if len(trans_cands) == 1:
                    return trans_cands[0]
                pool = trans_cands
            else:
                return None

            if ns_prefixes or open_list:
                active_prefs = tuple(p + "." for p in ns_prefixes) + tuple(
                    op + "." for op in open_list
                )
                ns_cands = [cid for cid in pool if decl_full_names[cid].startswith(active_prefs)]
                if len(ns_cands) == 1:
                    return ns_cands[0]
                if ns_cands:
                    pool = ns_cands

            if len(pool) <= 4:
                return pool[0]
            return None

        def _resolve_ref(
            ref: str,
            src_id: int,
            local_short: dict[str, list[int]],
            direct_short: dict[str, list[int]],
            ns_prefixes: list[str],
            open_list: list[str],
            partial_mode: bool,
            depth: int = 0,
        ) -> int | None:
            # 1. Exact full-name match
            exact = full_name_to_ids.get(ref)
            if exact is not None:
                hit = _pick_best(
                    exact,
                    src_id,
                    ns_prefixes,
                    open_list,
                    allow_unreached_exact=(partial_mode and "." in ref),
                )
                if hit is not None:
                    return hit

            # 2. Qualified by enclosing namespaces (innermost first)
            for pref in ns_prefixes:
                qhit = full_name_to_ids.get(f"{pref}.{ref}")
                if qhit is not None:
                    hit = _pick_best(
                        qhit,
                        src_id,
                        ns_prefixes,
                        open_list,
                        allow_unreached_exact=partial_mode,
                    )
                    if hit is not None:
                        return hit

            # 3. Qualified by opened namespaces
            for op in open_list:
                qhit = full_name_to_ids.get(f"{op}.{ref}")
                if qhit is not None:
                    hit = _pick_best(
                        qhit,
                        src_id,
                        ns_prefixes,
                        open_list,
                        allow_unreached_exact=partial_mode,
                    )
                    if hit is not None:
                        return hit

            # 4. Dotted reference: suffix match or projection stripping (`thm.mp`, `claimAll.left`)
            if "." in ref:
                last_seg = ref.rsplit(".", 1)[-1]
                scands = short_name_to_ids.get(last_seg)
                if scands is not None:
                    dot_ref = "." + ref
                    if isinstance(scands, int):
                        if decl_full_names[scands].endswith(dot_ref):
                            hit = _pick_best(
                                scands,
                                src_id,
                                ns_prefixes,
                                open_list,
                                allow_unreached_exact=partial_mode,
                            )
                            if hit is not None:
                                return hit
                    elif len(scands) <= _MAX_AMBIGUOUS_SHORT_CANDS * 4:
                        matched_list = [
                            cid for cid in scands if decl_full_names[cid].endswith(dot_ref)
                        ]
                        if matched_list:
                            hit = _pick_best(
                                matched_list[0] if len(matched_list) == 1 else matched_list,
                                src_id,
                                ns_prefixes,
                                open_list,
                                allow_unreached_exact=partial_mode,
                            )
                            if hit is not None:
                                return hit

                if depth < 2:
                    prefix_part = ref.rsplit(".", 1)[0]
                    if (
                        last_seg in _PROJECTION_SUFFIXES
                        or prefix_part in full_name_to_ids
                        or prefix_part in short_name_to_ids
                    ):
                        hit = _resolve_ref(
                            prefix_part,
                            src_id,
                            local_short,
                            direct_short,
                            ns_prefixes,
                            open_list,
                            partial_mode,
                            depth + 1,
                        )
                        if hit is not None:
                            return hit
                return None

            # 5. Unqualified short-name lookup: O(1) local -> O(1) direct import -> bounded transitive
            loc_cands = local_short.get(ref)
            if loc_cands:
                src_ln = decl_line[src_id]
                best = None
                best_ln = -1
                fallback = None
                for cid in loc_cands:
                    if cid == src_id:
                        continue
                    ln = decl_line[cid]
                    if ln < src_ln and ln > best_ln:
                        best = cid
                        best_ln = ln
                    elif fallback is None:
                        fallback = cid
                if best is not None:
                    return best
                if fallback is not None:
                    return fallback

            dir_cands = direct_short.get(ref)
            if dir_cands:
                if len(dir_cands) == 1:
                    if dir_cands[0] != src_id:
                        return dir_cands[0]
                elif len(dir_cands) <= 4:
                    for cid in dir_cands:
                        if cid != src_id:
                            return cid

            scands = short_name_to_ids.get(ref)
            if scands is not None:
                return _pick_best(
                    scands,
                    src_id,
                    ns_prefixes,
                    open_list,
                    allow_unreached_exact=False,
                )
            return None

        with gzip.GzipFile(fileobj=spill_raw, mode="rb") as spill_in:
            for raw_line in spill_in:
                mod_id, records = json.loads(raw_line)
                cur_mod_id = mod_id
                cur_mod_tbit = topo_bit[mod_id]
                cur_direct_set = direct_import_sets.get(mod_id, set())
                cur_bytes = None
                cur_bytes_len = 0
                cur_has_trans_deps = bool(cur_direct_set)
                partial_mode = mod_id in has_missing_project_imp

                # Build tiny O(1) short-name maps for current module & its direct imports
                local_short: dict[str, list[int]] = {}
                for did in mod_decl_ids.get(mod_id, ()):
                    sn = decl_short_names[did]
                    local_short.setdefault(sn, []).append(did)

                direct_short: dict[str, list[int]] = {}
                if cur_direct_set:
                    for dmod in cur_direct_set:
                        for did in mod_decl_ids.get(dmod, ()):
                            sn = decl_short_names[did]
                            direct_short.setdefault(sn, []).append(did)

                for src_id, ns_list, open_list, type_refs, proof_refs in records:
                    ns_prefixes: list[str] = []
                    if ns_list:
                        for k in range(len(ns_list), 0, -1):
                            ns_prefixes.append(".".join(ns_list[:k]))

                    seen_type: set[int] = set()
                    for ref in type_refs:
                        dst_id = _resolve_ref(
                            ref,
                            src_id,
                            local_short,
                            direct_short,
                            ns_prefixes,
                            open_list,
                            partial_mode,
                        )
                        if dst_id is not None and dst_id not in seen_type:
                            seen_type.add(dst_id)
                            edge_batch.append((src_id, dst_id, "type"))

                    seen_proof: set[int] = set()
                    for ref in proof_refs:
                        dst_id = _resolve_ref(
                            ref,
                            src_id,
                            local_short,
                            direct_short,
                            ns_prefixes,
                            open_list,
                            partial_mode,
                        )
                        if dst_id is not None and dst_id not in seen_proof:
                            seen_proof.add(dst_id)
                            edge_batch.append((src_id, dst_id, "proof"))

                    if len(edge_batch) >= edge_flush_size:
                        _flush_edges()

                mods_resolved += 1
                if progress_cb and mods_resolved % progress_every == 0:
                    progress_cb(
                        {
                            "phase": "pass2",
                            "modules_resolved": mods_resolved,
                            "edges": stats.edges_inserted,
                            "edges_inserted": stats.edges_inserted,
                            "elapsed_s": round(time.monotonic() - t0, 2),
                        }
                    )

        _flush_edges()

        t_p2 = time.monotonic()
        stats.pass2_seconds = round(t_p2 - t_p1, 3)
        stats.total_seconds = round(t_p2 - t0, 3)

        set_meta(conn, "ingest_source", stats.source)
        set_meta(conn, "ingest_mode", "source")
        set_meta(conn, "ingest_files", str(stats.files_ingested))
        set_meta(conn, "ingest_declarations", str(stats.declarations_inserted))
        set_meta(conn, "ingest_edges", str(stats.edges_inserted))
        set_meta(conn, "ingest_total_loc", str(stats.total_loc))
        set_meta(conn, "ingest_elapsed_s", str(stats.total_seconds))

        finalize_bulk(conn)
    finally:
        spill_raw.close()
        conn.close()

    return stats
