"""Import-safe and instance-aware Lean 4 proof pruning and project materialization."""

from __future__ import annotations

import glob
import io
import json
import re
import shutil
import sqlite3
import tarfile
import zlib
from collections import Counter, defaultdict, deque
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterator, Sequence

from proof_compressor.analyze.prune import resolve_roots
from proof_compressor.schema import connect_db, set_meta

VALID_MATERIALIZE_MODES = ("instance-aware", "import-closure", "decl-exact")

_CONFIG_FILENAMES = frozenset(
    {
        "lean-toolchain",
        "lakefile.toml",
        "lakefile.lean",
        "lake-manifest.json",
    }
)

_IMPLICIT_ATTR_RE = re.compile(
    r"@\[[^\]]*\b(?:simp|ext|aesop|norm_cast|push_cast|coe|positivity|measurability|"
    r"continuity|fun_prop|instance|default_instance|elab|macro|app_unexpander|delab)\b"
    r"|(?:\blocal\s+instance\b|\bscoped\s+(?:notation|macro|elab|instance|attribute)\b"
    r"|\battribute\s*\[[^\]]*\b(?:simp|instance|ext|coe)\b)",
    re.IGNORECASE,
)

_STRUCTURAL_LINE_RE = re.compile(
    r"^\s*(?:namespace\s+\S+|section(?:\s+\S+)?|end(?:\s+\S+)?)\s*(?:--.*)?$"
)

_IMPORT_LINE_RE = re.compile(r"^(\s*import\s+)([A-Za-z0-9_'.]+)(\s*(?:--.*)?)$")

_SAFE_STRIP_KINDS = frozenset({"theorem", "lemma"})
_IMPLICIT_KEEP_KINDS = frozenset({"instance", "class"})


@dataclass
class PrunePlan:
    """Computed module and declaration retention plan for a given pruning mode."""

    mode: str
    root_ids: list[int]
    root_names: list[str]
    root_module_ids: set[int]

    raw_project_modules: int
    import_closure_modules: set[int]
    decl_reachable_modules: set[int]
    instance_support_modules: set[int]
    barrel_bridge_modules: set[int]
    kept_modules: set[int]
    dropped_modules: set[int]

    kept_decl_ids: set[int]
    strippable_decl_ids_by_mod: dict[int, list[int]]

    mod_path: dict[int, str]
    mod_loc: dict[int, int]
    path_to_mid: dict[str, int]
    mod_imports: dict[int, list[int]]


@dataclass
class MaterializeReport:
    """Quantitative summary of import-safe / instance-aware pruning and materialization."""

    mode: str = "instance-aware"
    root_names: list[str] = field(default_factory=list)

    raw_modules: int = 0
    import_closure_modules: int = 0
    decl_reachable_modules: int = 0
    instance_support_modules: int = 0
    barrel_bridge_modules: int = 0
    kept_modules: int = 0
    dropped_modules: int = 0
    module_reduction_pct: float = 0.0

    raw_loc: int = 0
    import_closure_loc: int = 0
    decl_reachable_loc: int = 0
    kept_modules_raw_loc: int = 0
    intra_module_stripped_loc: int = 0
    materialized_loc: int = 0
    total_loc_reduction_pct: float = 0.0

    raw_declarations: int = 0
    reachable_declarations: int = 0
    instance_support_declarations: int = 0
    stripped_intra_module_declarations: int = 0
    kept_declarations: int = 0

    dropped_import_lines: int = 0
    rewritten_import_lines: int = 0
    files_written: int = 0
    config_files_copied: int = 0
    output_dir: str | None = None

    # Deep audit breakdown of imported-but-not-decl-reached modules
    unimported_dead_modules: int = 0
    unimported_dead_loc: int = 0
    imported_not_decl_reached_modules: int = 0
    imported_not_decl_reached_loc: int = 0
    imported_zero_decl_barrel_modules: int = 0
    imported_zero_decl_barrel_loc: int = 0
    imported_instance_class_modules: int = 0
    imported_instance_class_loc: int = 0
    imported_def_structure_modules: int = 0
    imported_def_structure_loc: int = 0
    imported_bookkeeping_lemma_modules: int = 0
    imported_bookkeeping_lemma_loc: int = 0
    imported_unused_theorem_modules: int = 0
    imported_unused_theorem_loc: int = 0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _open_db(db: sqlite3.Connection | str | Path) -> tuple[sqlite3.Connection, bool]:
    if isinstance(db, sqlite3.Connection):
        return db, False
    return connect_db(db), True


def _pct(part: int, whole: int) -> float:
    if whole <= 0:
        return 0.0
    return round(100.0 * part / whole, 2)


def _normalize_mod_name(raw_path: str) -> str:
    s = (raw_path or "").strip().replace("\\", "/")
    while s.startswith("./"):
        s = s[2:]
    for pref in ("lean/src/", "src/"):
        if s.startswith(pref):
            s = s[len(pref) :]
            break
    if s.endswith(".lean"):
        s = s[:-5]
    return s.replace("/", ".")


def compute_prune_plan(
    db: sqlite3.Connection | str | Path,
    *,
    roots: Sequence[str] | None = None,
    mode: str = "instance-aware",
) -> tuple[PrunePlan, MaterializeReport]:
    """Compute exact module and declaration retention plan under the chosen pruning mode."""
    if mode not in VALID_MATERIALIZE_MODES:
        raise ValueError(f"Unsupported mode {mode!r}; choose from {VALID_MATERIALIZE_MODES}")

    conn, should_close = _open_db(db)
    try:
        cur = conn.cursor()

        mod_path: dict[int, str] = {}
        mod_loc: dict[int, int] = {}
        mod_is_ml: dict[int, int] = {}
        path_to_mid: dict[str, int] = {}

        for mid, path, loc, is_ml in cur.execute(
            "SELECT id, path, loc, is_mathlib FROM modules"
        ):
            mid_i = int(mid)
            p = path or ""
            mod_path[mid_i] = p
            mod_loc[mid_i] = int(loc or 0)
            mod_is_ml[mid_i] = int(is_ml or 0)
            if p:
                path_to_mid[p] = mid_i
                path_to_mid[_normalize_mod_name(p)] = mid_i

        project_mids = {m for m, ml in mod_is_ml.items() if ml == 0}

        # Load module_imports
        mod_imports: dict[int, list[int]] = defaultdict(list)
        for src_mid, dst_path, dst_mid in cur.execute(
            "SELECT src_module_id, dst_module_path, dst_module_id FROM module_imports"
        ):
            tmid = int(dst_mid) if dst_mid is not None else path_to_mid.get(dst_path or "")
            if tmid is None and dst_path:
                tmid = path_to_mid.get(_normalize_mod_name(dst_path))
            if tmid is not None and tmid in project_mids and int(src_mid) in project_mids:
                mod_imports[int(src_mid)].append(tmid)

        # Load project declarations
        decl_mod: dict[int, int] = {}
        decl_kind: dict[int, str] = {}
        decl_loc: dict[int, int] = {}
        decl_bk: dict[int, int] = {}
        decl_name: dict[int, str] = {}
        mod_to_decls: dict[int, list[int]] = defaultdict(list)
        mod_kinds: dict[int, Counter[str]] = defaultdict(Counter)
        mod_bk_cnt: Counter[int] = Counter()

        for did, name, mid, kind, bloc, is_ml, is_bk in cur.execute(
            "SELECT id, name, module_id, kind, body_loc, is_mathlib, is_bookkeeping "
            "FROM declarations"
        ):
            if int(is_ml or 0) != 0:
                continue
            did_i = int(did)
            mid_i = int(mid or 0)
            k = (kind or "").lower()
            bl = int(bloc or 0)
            bk = int(is_bk or 0)
            decl_mod[did_i] = mid_i
            decl_kind[did_i] = k
            decl_loc[did_i] = bl
            decl_bk[did_i] = bk
            decl_name[did_i] = name or ""
            mod_to_decls[mid_i].append(did_i)
            mod_kinds[mid_i][k] += 1
            if bk:
                mod_bk_cnt[mid_i] += 1

        resolved_roots = resolve_roots(conn, roots)
        root_ids = [r[0] for r in resolved_roots]
        root_names = [r[1] for r in resolved_roots]
        root_mod_ids = {
            decl_mod[rid] for rid in root_ids if rid in decl_mod and decl_mod[rid] in project_mids
        }

        # Build declaration outgoing adjacency (src -> dst) restricted to project decls
        out_adj: dict[int, list[int]] = defaultdict(list)
        prev_s = -1
        prev_d = -1
        for src_id, dst_id in cur.execute(
            "SELECT src_id, dst_id FROM edges ORDER BY src_id, dst_id"
        ):
            if src_id == dst_id or (src_id == prev_s and dst_id == prev_d):
                continue
            prev_s = src_id
            prev_d = dst_id
            if src_id in decl_mod and dst_id in decl_mod:
                out_adj[src_id].append(dst_id)

        # 1. Exact declaration reachability BFS from root_ids
        decl_reach: set[int] = set()
        q_decl: deque[int] = deque()
        for rid in root_ids:
            if rid in decl_mod and rid not in decl_reach:
                decl_reach.add(rid)
                q_decl.append(rid)
        while q_decl:
            u = q_decl.popleft()
            for v in out_adj.get(u, ()):
                if v not in decl_reach:
                    decl_reach.add(v)
                    q_decl.append(v)

        decl_reach_mods = {decl_mod[d] for d in decl_reach if decl_mod[d] in project_mids} | root_mod_ids

        # 2. Transitive module-import closure from root_mod_ids (and decl_reach_mods if imports missing on root)
        imp_closure: set[int] = set()
        q_mod: deque[int] = deque()
        seed_mods = root_mod_ids if root_mod_ids else decl_reach_mods
        for m in seed_mods:
            if m in project_mids and m not in imp_closure:
                imp_closure.add(m)
                q_mod.append(m)
        while q_mod:
            m = q_mod.popleft()
            for nb in mod_imports.get(m, ()):
                if nb not in imp_closure:
                    imp_closure.add(nb)
                    q_mod.append(nb)

        # Ensure any declaration-reachable module is also included in imp_closure view
        imp_closure_or_decl = imp_closure | decl_reach_mods

        # 3. Classify imported-but-not-decl-reached modules
        diff_mods = imp_closure - decl_reach_mods
        unimported_mods = project_mids - imp_closure_or_decl

        zero_decl_mods: set[int] = set()
        instance_class_mods: set[int] = set()
        def_struct_mods: set[int] = set()
        bk_lemma_mods: set[int] = set()
        unused_thm_mods: set[int] = set()

        for m in diff_mods:
            dlist = mod_to_decls.get(m, [])
            if not dlist:
                zero_decl_mods.add(m)
            elif mod_kinds[m]["instance"] > 0 or mod_kinds[m]["class"] > 0:
                instance_class_mods.add(m)
            elif any(
                mod_kinds[m][k] > 0
                for k in ("def", "abbrev", "structure", "inductive", "axiom", "opaque", "constant")
            ):
                def_struct_mods.add(m)
            elif mod_bk_cnt[m] > 0:
                bk_lemma_mods.add(m)
            else:
                unused_thm_mods.add(m)

        # 4. In instance-aware mode:
        # Keep decl_reach_mods + transitively imported instance/class modules + all prerequisite
        # declarations/modules needed to compile those instance/class modules!
        instance_support_decls: set[int] = set()
        instance_support_mods: set[int] = set()
        barrel_bridge_mods: set[int] = set()

        if mode in ("instance-aware", "import-closure"):
            # Seed with all declarations in imported modules that contain instances/classes
            # plus any instance/class declarations inside already-reachable modules
            q_inst: deque[int] = deque()
            for m in imp_closure_or_decl:
                if mod_kinds[m]["instance"] > 0 or mod_kinds[m]["class"] > 0:
                    instance_support_mods.add(m)
                    for d in mod_to_decls.get(m, ()):
                        if (
                            decl_kind[d] in _IMPLICIT_KEEP_KINDS
                            and d not in decl_reach
                            and d not in instance_support_decls
                        ):
                            instance_support_decls.add(d)
                            q_inst.append(d)

            # Traverse edges from instance module declarations so every helper lemma/def
            # required to compile a kept instance module is ALSO kept!
            while q_inst:
                u = q_inst.popleft()
                for v in out_adj.get(u, ()):
                    if v not in decl_reach and v not in instance_support_decls:
                        instance_support_decls.add(v)
                        instance_support_mods.add(decl_mod[v])
                        q_inst.append(v)

            # Also keep zero-declaration barrel/notation modules that transitively re-export
            # kept modules (e.g. Main -> MainTheoremsAll -> MainTheoremsCritical -> MainTheorems)
            core_kept = set(decl_reach_mods | instance_support_mods)
            added_barrel = True
            while added_barrel:
                added_barrel = False
                for m in zero_decl_mods:
                    if m not in barrel_bridge_mods and any(
                        nb in core_kept or nb in barrel_bridge_mods
                        for nb in mod_imports.get(m, ())
                    ):
                        barrel_bridge_mods.add(m)
                        added_barrel = True

        if mode == "import-closure":
            kept_modules = set(imp_closure_or_decl)
        elif mode == "instance-aware":
            kept_modules = decl_reach_mods | instance_support_mods | barrel_bridge_mods
        else:  # decl-exact
            kept_modules = set(decl_reach_mods)

        dropped_modules = project_mids - kept_modules
        kept_decl_ids = set(decl_reach) | set(instance_support_decls)

        # Identify safely strippable intra-module dead theorem/lemma declarations inside kept_modules
        strippable_by_mod: dict[int, list[int]] = defaultdict(list)
        stripped_intra_loc = 0
        stripped_intra_cnt = 0

        for m in kept_modules:
            for d in mod_to_decls.get(m, ()):
                if d in kept_decl_ids:
                    continue
                if decl_kind[d] in _SAFE_STRIP_KINDS:
                    strippable_by_mod[m].append(d)
                    stripped_intra_loc += decl_loc[d]
                    stripped_intra_cnt += 1
                else:
                    # Non-theorem declarations (defs/instances/structures) in kept modules stay kept
                    kept_decl_ids.add(d)

        raw_loc = sum(mod_loc[m] for m in project_mids)
        imp_loc = sum(mod_loc[m] for m in imp_closure_or_decl)
        decl_loc_sum = sum(mod_loc[m] for m in decl_reach_mods)
        kept_raw_loc = sum(mod_loc[m] for m in kept_modules)
        est_mat_loc = max(0, kept_raw_loc - stripped_intra_loc)

        report = MaterializeReport(
            mode=mode,
            root_names=root_names,
            raw_modules=len(project_mids),
            import_closure_modules=len(imp_closure_or_decl),
            decl_reachable_modules=len(decl_reach_mods),
            instance_support_modules=len(instance_support_mods - decl_reach_mods),
            barrel_bridge_modules=len(barrel_bridge_mods - decl_reach_mods - instance_support_mods),
            kept_modules=len(kept_modules),
            dropped_modules=len(dropped_modules),
            module_reduction_pct=_pct(len(dropped_modules), len(project_mids)),
            raw_loc=raw_loc,
            import_closure_loc=imp_loc,
            decl_reachable_loc=decl_loc_sum,
            kept_modules_raw_loc=kept_raw_loc,
            intra_module_stripped_loc=stripped_intra_loc,
            materialized_loc=est_mat_loc,
            total_loc_reduction_pct=_pct(raw_loc - est_mat_loc, raw_loc),
            raw_declarations=len(decl_mod),
            reachable_declarations=len(decl_reach),
            instance_support_declarations=len(instance_support_decls),
            stripped_intra_module_declarations=stripped_intra_cnt,
            kept_declarations=len(kept_decl_ids),
            unimported_dead_modules=len(unimported_mods),
            unimported_dead_loc=sum(mod_loc[m] for m in unimported_mods),
            imported_not_decl_reached_modules=len(diff_mods),
            imported_not_decl_reached_loc=sum(mod_loc[m] for m in diff_mods),
            imported_zero_decl_barrel_modules=len(zero_decl_mods),
            imported_zero_decl_barrel_loc=sum(mod_loc[m] for m in zero_decl_mods),
            imported_instance_class_modules=len(instance_class_mods),
            imported_instance_class_loc=sum(mod_loc[m] for m in instance_class_mods),
            imported_def_structure_modules=len(def_struct_mods),
            imported_def_structure_loc=sum(mod_loc[m] for m in def_struct_mods),
            imported_bookkeeping_lemma_modules=len(bk_lemma_mods),
            imported_bookkeeping_lemma_loc=sum(mod_loc[m] for m in bk_lemma_mods),
            imported_unused_theorem_modules=len(unused_thm_mods),
            imported_unused_theorem_loc=sum(mod_loc[m] for m in unused_thm_mods),
        )

        plan = PrunePlan(
            mode=mode,
            root_ids=root_ids,
            root_names=root_names,
            root_module_ids=root_mod_ids,
            raw_project_modules=len(project_mids),
            import_closure_modules=imp_closure_or_decl,
            decl_reachable_modules=decl_reach_mods,
            instance_support_modules=instance_support_mods,
            barrel_bridge_modules=barrel_bridge_mods,
            kept_modules=kept_modules,
            dropped_modules=dropped_modules,
            kept_decl_ids=kept_decl_ids,
            strippable_decl_ids_by_mod=dict(strippable_by_mod),
            mod_path=mod_path,
            mod_loc=mod_loc,
            path_to_mid=path_to_mid,
            mod_imports=dict(mod_imports),
        )
        return plan, report
    finally:
        if should_close:
            conn.close()


def _replacement_imports_for_dropped(
    dropped_mid: int,
    kept_modules: set[int],
    mod_imports: dict[int, list[int]],
    mod_path: dict[int, str],
) -> list[str]:
    """Find kept modules transitively re-exported through a dropped barrel/intermediate module."""
    found: list[str] = []
    visited: set[int] = {dropped_mid}
    q: deque[int] = deque([dropped_mid])
    while q and len(found) < 32:
        cur = q.popleft()
        for nb in mod_imports.get(cur, ()):
            if nb in visited:
                continue
            visited.add(nb)
            if nb in kept_modules:
                found.append(_normalize_mod_name(mod_path[nb]))
            else:
                q.append(nb)
    return found


def transform_lean_source(
    source_text: str,
    *,
    module_id: int,
    plan: PrunePlan,
    decl_spans: list[tuple[int, int, str, int]],
    strip_dead_decls: bool = True,
    rewrite_imports: bool = True,
) -> tuple[str, int, int, int]:
    """Rewrite import headers and strip dead intra-module theorems/lemmas from a `.lean` file.

    `decl_spans` is a list of `(decl_id, start_line, end_line_or_kind, ...)` ->
    specifically `(decl_id, start_line, end_line, kind_is_strippable)`.
    Returns `(new_source, stripped_decls, dropped_imports, rewritten_imports)`.
    """
    lines = source_text.splitlines()
    n_lines = len(lines)
    if n_lines == 0:
        return source_text, 0, 0, 0

    # 1. Determine line indices (0-based) to strip for dead intra-module declarations
    strip_line_mask = bytearray(n_lines)
    stripped_decls = 0

    if strip_dead_decls and decl_spans:
        kept_line_mask = bytearray(n_lines)
        for did, s_line, e_line, is_strip_cand in decl_spans:
            if not is_strip_cand or did in plan.kept_decl_ids:
                s0 = max(0, s_line - 1)
                e0 = min(n_lines - 1, max(s0, e_line - 1))
                for idx in range(s0, e0 + 1):
                    kept_line_mask[idx] = 1

        for did, s_line, e_line, is_strip_cand in decl_spans:
            if not is_strip_cand or did in plan.kept_decl_ids:
                continue
            if s_line <= 0 or e_line < s_line:
                continue
            s0 = max(0, s_line - 1)
            e0 = min(n_lines - 1, e_line - 1)

            # Expand upward to include immediately preceding @[...] attribute lines and /-- ... -/ docstring
            ext_s0 = s0
            while ext_s0 > 0:
                prev = lines[ext_s0 - 1].strip()
                if prev.startswith("@["):
                    ext_s0 -= 1
                elif prev.endswith("-/"):
                    # Walk back to start of docstring `/--`
                    doc_s = ext_s0 - 1
                    while doc_s >= 0 and "/--" not in lines[doc_s] and "/-" not in lines[doc_s]:
                        doc_s -= 1
                    if doc_s >= 0 and "/--" in lines[doc_s]:
                        ext_s0 = doc_s
                    break
                else:
                    break

            # Safety checks: never strip if overlapping a kept declaration or containing implicit attributes
            if any(kept_line_mask[i] for i in range(ext_s0, e0 + 1)):
                continue
            block_text = "\n".join(lines[ext_s0 : e0 + 1])
            if _IMPLICIT_ATTR_RE.search(block_text):
                continue

            for i in range(ext_s0, e0 + 1):
                if not _STRUCTURAL_LINE_RE.match(lines[i]):
                    strip_line_mask[i] = 1
            stripped_decls += 1

    # 2. Rewrite imports and emit kept lines
    out_lines: list[str] = []
    seen_imports: set[str] = set()
    dropped_imports = 0
    rewritten_imports = 0
    self_mod_name = _normalize_mod_name(plan.mod_path.get(module_id, ""))

    for idx, line in enumerate(lines):
        if strip_line_mask[idx]:
            continue
        if rewrite_imports:
            m = _IMPORT_LINE_RE.match(line)
            if m:
                prefix, imp_target, suffix = m.group(1), m.group(2), m.group(3)
                target_mid = plan.path_to_mid.get(imp_target) or plan.path_to_mid.get(
                    _normalize_mod_name(imp_target)
                )
                if target_mid is None:
                    # External / Mathlib import -> keep
                    if imp_target not in seen_imports:
                        seen_imports.add(imp_target)
                        out_lines.append(line)
                    continue
                if target_mid in plan.kept_modules:
                    if imp_target not in seen_imports and imp_target != self_mod_name:
                        seen_imports.add(imp_target)
                        out_lines.append(line)
                    continue
                # target_mid was dropped! Check if it was a barrel bridging to kept modules
                replacements = _replacement_imports_for_dropped(
                    target_mid,
                    plan.kept_modules,
                    plan.mod_imports,
                    plan.mod_path,
                )
                added_any = False
                for rep in replacements:
                    if rep not in seen_imports and rep != self_mod_name:
                        seen_imports.add(rep)
                        out_lines.append(f"{prefix}{rep}{suffix}")
                        added_any = True
                if added_any:
                    rewritten_imports += 1
                else:
                    dropped_imports += 1
                continue
        out_lines.append(line)

    text = "\n".join(out_lines)
    if source_text.endswith("\n"):
        text += "\n"
    stripped_nonblank_lines = sum(
        1 for idx in range(n_lines) if strip_line_mask[idx] and lines[idx].strip()
    ) + dropped_imports
    return text, stripped_decls, stripped_nonblank_lines, dropped_imports, rewritten_imports


class _ConcatPartStream(io.RawIOBase):
    """Zero-disk-extraction sequential reader across concatenated `.tar.gz.part*` files."""

    def __init__(self, part_paths: Sequence[Path]) -> None:
        self._parts = list(part_paths)
        self._idx = 0
        self._fh = open(self._parts[0], "rb") if self._parts else None

    def readable(self) -> bool:
        return True

    def readinto(self, b: Any) -> int:
        if self._fh is None:
            return 0
        total = 0
        mv = memoryview(b)
        while total < len(mv) and self._fh is not None:
            n = self._fh.readinto(mv[total:])
            if n:
                total += n
            else:
                self._fh.close()
                self._idx += 1
                if self._idx < len(self._parts):
                    self._fh = open(self._parts[self._idx], "rb")
                else:
                    self._fh = None
        return total

    def close(self) -> None:
        if self._fh is not None:
            self._fh.close()
            self._fh = None
        super().close()


def _resolve_source_parts(source: str | Path | Sequence[str | Path]) -> tuple[str, list[Path]]:
    if isinstance(source, (list, tuple)):
        paths = [Path(p) for p in source]
        return "parts", paths
    s = str(source)
    if any(ch in s for ch in ("*", "?", "[")):
        matched = sorted(Path(p) for p in glob.glob(s))
        if not matched:
            raise FileNotFoundError(f"No files matched glob: {s}")
        return "parts", matched
    p = Path(s)
    if p.is_dir():
        return "dir", [p]
    if re.search(r"\.part\d+$", p.name):
        base = re.sub(r"\.part\d+$", ".part*", str(p))
        siblings = sorted(Path(x) for x in glob.glob(base))
        return "parts", siblings or [p]
    return "archive", [p]


def _iter_source_entries(
    source: str | Path | Sequence[str | Path],
) -> Iterator[tuple[str, bytes]]:
    kind, paths = _resolve_source_parts(source)
    if kind == "dir":
        root = paths[0]
        for fpath in sorted(root.rglob("*")):
            if not fpath.is_file():
                continue
            rel = fpath.relative_to(root).as_posix()
            if rel.startswith(".lake/") or "/.lake/" in rel or rel.startswith(".git/"):
                continue
            if fpath.name in _CONFIG_FILENAMES or fpath.suffix == ".lean":
                yield rel, fpath.read_bytes()
        return

    raw_stream = _ConcatPartStream(paths)
    buf_stream = io.BufferedReader(raw_stream, buffer_size=1 << 20)
    try:
        with tarfile.open(fileobj=buf_stream, mode="r|*") as tf:
            for member in tf:
                if not member.isfile():
                    continue
                name = member.name.lstrip("./")
                base = name.rsplit("/", 1)[-1]
                if base in _CONFIG_FILENAMES or name.endswith(".lean"):
                    extracted = tf.extractfile(member)
                    if extracted is not None:
                        yield name, extracted.read()
    except (tarfile.ReadError, zlib.error, EOFError):
        # Allow partial prefix archives to close cleanly
        pass
    finally:
        buf_stream.close()


def _strip_archive_root_prefix(rel_path: str) -> str:
    norm = rel_path.replace("\\", "/").lstrip("./")
    if norm.startswith("lean/"):
        return norm[5:]
    return norm


def materialize_project(
    db: sqlite3.Connection | str | Path,
    *,
    source: str | Path | Sequence[str | Path] | None = None,
    output_dir: str | Path | None = None,
    roots: Sequence[str] | None = None,
    mode: str = "instance-aware",
    strip_dead_decls: bool = True,
    rewrite_imports: bool = True,
    dry_run: bool = False,
    max_files: int | None = None,
) -> MaterializeReport:
    """Compute pruning plan and optionally stream-materialize a compilable pruned Lean 4 project."""
    conn, should_close = _open_db(db)
    try:
        plan, report = compute_prune_plan(conn, roots=roots, mode=mode)

        if dry_run or source is None or output_dir is None:
            try:
                set_meta(conn, f"analysis_materialize_{mode}", json.dumps(report.to_dict()))
                conn.commit()
            except sqlite3.OperationalError:
                pass
            return report

        out_root = Path(output_dir)
        out_root.mkdir(parents=True, exist_ok=True)
        report.output_dir = str(out_root)

        # Preload declaration line spans for kept modules
        cur = conn.cursor()
        spans_by_mod: dict[int, list[tuple[int, int, int, bool]]] = defaultdict(list)
        for did, mid, kind, s_line, e_line in cur.execute(
            "SELECT id, module_id, kind, start_line, end_line FROM declarations WHERE is_mathlib = 0"
        ):
            mid_i = int(mid or 0)
            if mid_i not in plan.kept_modules:
                continue
            k = (kind or "").lower()
            spans_by_mod[mid_i].append(
                (
                    int(did),
                    int(s_line or 0),
                    int(e_line or 0),
                    k in _SAFE_STRIP_KINDS,
                )
            )

        files_written = 0
        configs_copied = 0
        total_stripped_lines = 0
        total_stripped_decls = 0
        total_dropped_imps = 0
        total_rewritten_imps = 0
        seen_lean = 0

        for rel_path, raw_bytes in _iter_source_entries(source):
            clean_rel = _strip_archive_root_prefix(rel_path)
            base_name = clean_rel.rsplit("/", 1)[-1]

            if base_name in _CONFIG_FILENAMES and "/" not in clean_rel:
                dest = out_root / clean_rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(raw_bytes)
                configs_copied += 1
                continue

            if not clean_rel.endswith(".lean"):
                continue

            seen_lean += 1
            if max_files is not None and seen_lean > max_files:
                break

            mod_key = _normalize_mod_name(clean_rel)
            mid = plan.path_to_mid.get(clean_rel) or plan.path_to_mid.get(mod_key) or plan.path_to_mid.get(rel_path)
            if mid is None or mid not in plan.kept_modules:
                continue

            src_text = raw_bytes.decode("utf-8", errors="replace")
            new_text, s_decls, s_lines, d_imps, r_imps = transform_lean_source(
                src_text,
                module_id=mid,
                plan=plan,
                decl_spans=spans_by_mod.get(mid, []),
                strip_dead_decls=strip_dead_decls,
                rewrite_imports=rewrite_imports,
            )

            dest = out_root / clean_rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(new_text, encoding="utf-8")

            files_written += 1
            total_stripped_lines += s_lines
            total_stripped_decls += s_decls
            total_dropped_imps += d_imps
            total_rewritten_imps += r_imps

        if files_written > 0:
            report.files_written = files_written
            report.config_files_copied = configs_copied
            report.intra_module_stripped_loc = total_stripped_lines
            report.materialized_loc = max(0, report.kept_modules_raw_loc - total_stripped_lines)
            report.stripped_intra_module_declarations = total_stripped_decls
            report.dropped_import_lines = total_dropped_imps
            report.rewritten_import_lines = total_rewritten_imps
            report.total_loc_reduction_pct = _pct(report.raw_loc - report.materialized_loc, report.raw_loc)

        try:
            set_meta(conn, f"analysis_materialize_{mode}", json.dumps(report.to_dict()))
            conn.commit()
        except sqlite3.OperationalError:
            pass
        return report
    finally:
        if should_close:
            conn.close()
