"""Phase A & B Lean 4 module fusion, topological bundling, and post-merge duplicate consolidation.

Compresses large fragmented Lean 4 repositories (tens of thousands of small modules)
into balanced, cycle-free compilation units up to ``target_module_loc`` while strictly
preserving Lean 4 compilation semantics:

- **Phase A1 (Single-consumer chain fusion)**: Fuses any mergeable module ``C`` whose
  sole consumer is ``P`` (in the same ``lean_lib`` glob boundary, with disjoint public
  and ``private`` declaration names, and combined LOC <= ``target_module_loc``).
- **Phase A2 (Duplicate-aware convex antichain bundling)**: Groups remaining mergeable
  bundles by ``(lean_lib_root, topological_layer)`` (an exact antichain in the DAG,
  mathematically guaranteed 0 import cycles), co-locating modules that share exact
  duplicate theorem hashes, and packs them up to ``target_module_loc``.
- **Phase A3 (Second-pass chain fusion)**: Re-runs single-consumer fusion on the A2
  quotient DAG.
- **Lean 4 section/scope hygiene**: Wraps each merged unit in ``section __pc_u_i ...
  end __pc_u_i`` with any unclosed ``section`` / ``noncomputable section`` /
  ``namespace`` scopes explicitly balanced before ``end __pc_u_i``, keeps ``Main``,
  ``Statements``, and syntax/macro/elab/export modules standalone, and enforces
  disjoint ``private`` and public declaration names within every bundle.
- **Phase B (Post-merge exact-duplicate consolidation)**: Re-parses merged bundles to
  locate exact surviving line spans, consolidates in-bundle and transitively-imported
  duplicates (0 new imports), and optionally performs cycle-free cross-bundle
  delegation (``topo_rank(C) < topo_rank(D)``) for remaining sibling-branch duplicates.
"""

from __future__ import annotations

import re
import sqlite3
from collections import defaultdict, deque
from dataclasses import asdict, dataclass
from typing import TYPE_CHECKING, Any, Sequence

from proof_compressor.analyze.consolidate import (
    ConsolidationOp,
    _extract_decl_source_context,
    apply_consolidations_to_lines,
    build_delegation_rhs,
    parse_signature_structure,
)
from proof_compressor.ingest.lean_parser import (
    parse_lean_source,
    strip_comments_and_extract_docstrings,
)

if TYPE_CHECKING:
    from proof_compressor.analyze.materialize import PrunePlan


_IMPORT_LINE_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_'.\u0080-\uffff]+)\s*(?:--.*)?$"
)

_STANDALONE_CMD_RE = re.compile(
    r"^\s*(?:(?:local|scoped)\s+)?(?:syntax|macro|macro_rules|elab|elab_rules|"
    r"declare_syntax_cat|initialize|builtin_initialize|register_simp_attr|"
    r"suppress_compilation|run_cmd|export|add_decl_doc)\b"
    r"|^\s*(?:scoped\s+)?(?:notation|infixl?|infixr|prefix|postfix)\b"
)

_NONLOCAL_ATTR_OR_INST_RE = re.compile(
    r"^\s*(?:attribute\s*\[(?![^\]]*\blocal\b)[^\]]+\]"
    r"|(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|scoped|local)\s+)*instance\b)"
)

_NAMESPACE_LINE_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*)")
_SECTION_LINE_RE = re.compile(
    r"^(?:noncomputable\s+)?section(?:\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*))?\s*$"
)
_END_LINE_RE = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*))?\s*$")
_MUTUAL_LINE_RE = re.compile(r"^mutual\s*$")


@dataclass
class MergeUnit:
    """Single original `.lean` module prepared for merging."""

    mod_name: str
    rel_path: str
    lib_root: str
    imports: list[str]
    body_lines: list[str]
    unclosed_ends: list[str]
    nonblank_loc: int
    decl_names: set[str]
    private_names: set[str]
    is_standalone: bool
    has_nonlocal_attr_or_inst: bool
    dup_group_key: int | None = None
    # Namespaces this unit declares, and the project namespaces that would hijack one of
    # its `open X` lines (`open Real` inside `namespace A.B` resolves to `A.B.Real` or
    # `A.Real` when visible). Units with intersecting sets must not share a file.
    declared_namespaces: frozenset[str] = frozenset()
    open_shadow_keys: frozenset[str] = frozenset()


@dataclass
class MergeReport:
    """Quantitative summary of Phase A module fusion and Phase B duplicate consolidation."""

    target_module_loc: int = 1400
    input_modules: int = 0
    standalone_modules: int = 0
    phase_a1_fused_modules: int = 0
    after_phase_a1_modules: int = 0
    after_phase_a2_modules: int = 0
    phase_a3_fused_modules: int = 0
    output_modules: int = 0
    module_reduction_pct: float = 0.0

    input_nonblank_loc: int = 0
    output_nonblank_loc: int = 0
    output_total_lines: int = 0
    loc_saved_by_merge: int = 0
    input_import_lines: int = 0
    output_import_lines: int = 0
    eliminated_import_lines: int = 0

    max_bundle_loc: int = 0
    mean_bundle_loc: float = 0.0
    max_dag_layer: int = 0
    dangling_imports: int = 0
    cycle_count: int = 0

    phase_b_same_bundle_consolidations: int = 0
    phase_b_imported_bundle_consolidations: int = 0
    phase_b_cross_bundle_consolidations: int = 0
    phase_b_total_consolidations: int = 0
    phase_b_saved_loc: int = 0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def parse_lakefile_lib_globs(lakefile_toml_text: str | None) -> list[tuple[str, list[str]]]:
    """Parse ``[[lean_lib]]`` name and ``globs``/``roots`` from ``lakefile.toml``."""
    if not lakefile_toml_text:
        return []

    libs: list[tuple[str, list[str]]] = []
    cur_name: str | None = None
    cur_patterns: list[str] = []

    def _flush() -> None:
        nonlocal cur_name, cur_patterns
        if cur_name:
            libs.append((cur_name, list(cur_patterns)))
        cur_name = None
        cur_patterns = []

    for raw in lakefile_toml_text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line == "[[lean_lib]]":
            _flush()
            continue
        if line.startswith("["):
            _flush()
            continue
        if "=" in line:
            k, v = line.split("=", 1)
            k = k.strip()
            v = v.strip()
            if k == "name":
                m = re.match(r'^["\']([^"\']+)["\']', v)
                if m:
                    cur_name = m.group(1)
            elif k in ("globs", "roots"):
                cur_patterns.extend(re.findall(r'["\']([^"\']+)["\']', v))
    _flush()
    return libs


def _glob_to_bucket(mod_name: str, libs: list[tuple[str, list[str]]]) -> str:
    """Map ``mod_name`` to the exact ``lean_lib`` glob prefix that owns it."""
    if mod_name in ("Main", "Statements"):
        return mod_name

    best_prefix: str | None = None
    for lib_name, patterns in libs:
        for pat in patterns:
            if pat.endswith(".+"):
                pref = pat[:-2]
                if mod_name == pref or mod_name.startswith(pref + "."):
                    if best_prefix is None or len(pref) > len(best_prefix):
                        best_prefix = pref
            elif pat.endswith(".*"):
                pref = pat[:-2]
                if mod_name.startswith(pref + ".") and "." not in mod_name[len(pref) + 1 :]:
                    if best_prefix is None or len(pref) > len(best_prefix):
                        best_prefix = pref
            elif mod_name == pat:
                return f"__root__{lib_name}:{pat}"
    if best_prefix is not None:
        return best_prefix

    parts = mod_name.split(".")
    if parts[0] == "GroundTheory" and len(parts) >= 2:
        return f"GroundTheory.{parts[1]}"
    return parts[0]


def _extract_imports_and_body(source_text: str) -> tuple[list[str], list[str]]:
    """Split a Lean 4 module into its import list and body lines."""
    imports: list[str] = []
    body_lines: list[str] = []
    in_header = True
    comment_depth = 0
    for line in source_text.splitlines():
        if in_header:
            s = line.strip()
            # Leading copyright/module-doc comments may precede the imports. Keep them in
            # the body (comments are harmless inside a section) and keep scanning, or the
            # imports below them would land mid-file inside `section __pc_u_*`.
            if comment_depth or s.startswith("/-"):
                comment_depth = max(0, comment_depth + s.count("/-") - s.count("-/"))
                body_lines.append(line)
                continue
            if s.startswith("--"):
                body_lines.append(line)
                continue
            m = _IMPORT_LINE_RE.match(line)
            if m:
                imports.append(m.group(1))
                continue
            if not s:
                continue
            in_header = False
        body_lines.append(line)

    while body_lines and not body_lines[0].strip():
        body_lines.pop(0)
    while body_lines and not body_lines[-1].strip():
        body_lines.pop()
    return imports, body_lines


def _compute_unclosed_ends(body_lines: list[str]) -> tuple[list[str], bool]:
    """Compute exact ``end`` lines needed to close any unclosed ``section``/``namespace`` scopes.

    Returns ``(closing_lines, ok)`` where ``ok`` is False if a mismatched ``end`` or
    unclosed ``mutual`` was encountered (making the module safer to keep standalone).
    """
    cleaned, _ = strip_comments_and_extract_docstrings("\n".join(body_lines))
    stack: list[tuple[str, list[str]]] = []
    in_mutual = False

    for line in cleaned.splitlines():
        if not line or line[0] in (" ", "\t"):
            continue
        st = line.strip()
        if not st:
            continue
        if _MUTUAL_LINE_RE.match(st):
            in_mutual = True
            continue
        em = _END_LINE_RE.match(st)
        if em:
            if in_mutual and not em.group(1):
                in_mutual = False
                continue
            ename = em.group(1)
            if not stack:
                return [], False
            if not ename:
                stack.pop()
                continue
            rem = ename.split(".")
            while rem and stack:
                k, segs = stack[-1]
                if k == "section":
                    stack.pop()
                    if segs == rem:
                        rem.clear()
                    elif segs and len(rem) >= len(segs) and rem[-len(segs) :] == segs:
                        del rem[-len(segs) :]
                    continue
                if not segs:
                    stack.pop()
                    continue
                if segs == rem:
                    stack.pop()
                    rem.clear()
                elif len(segs) > len(rem) and segs[-len(rem) :] == rem:
                    stack[-1] = (k, segs[:-len(rem)])
                    rem.clear()
                elif len(rem) > len(segs) and rem[-len(segs) :] == segs:
                    stack.pop()
                    del rem[-len(segs) :]
                else:
                    return [], False
            if rem:
                return [], False
            continue
        nm = _NAMESPACE_LINE_RE.match(st)
        if nm:
            stack.append(("namespace", nm.group(1).split(".")))
            continue
        sm = _SECTION_LINE_RE.match(st)
        if sm:
            segs = sm.group(1).split(".") if sm.group(1) else []
            stack.append(("section", segs))
            continue

    if in_mutual:
        return [], False

    closing: list[str] = []
    for _k, segs in reversed(stack):
        if segs:
            closing.append(f"end {'.'.join(segs)}")
        else:
            closing.append("end")
    return closing, True


def _analyze_unit(
    mod_name: str,
    rel_path: str,
    source_text: str,
    *,
    lib_globs: list[tuple[str, list[str]]],
    root_mods: set[str],
    dup_group_key: int | None = None,
) -> MergeUnit:
    imports, body_lines = _extract_imports_and_body(source_text)
    unclosed_ends, scopes_ok = _compute_unclosed_ends(body_lines)

    parsed = parse_lean_source(source_text, mod_name)
    decl_names: set[str] = set()
    private_names: set[str] = set()
    declared_ns: set[str] = set()
    shadow_keys: set[str] = set()
    for d in parsed.declarations:
        decl_names.add(d.name)
        if d.is_private:
            private_names.add(d.name)
        segs = d.name.split(".")
        for i in range(1, len(segs) + 1):
            declared_ns.add(".".join(segs[:i]))
        ns = list(d.namespace_stack)
        for opened in d.open_namespaces:
            for i in range(1, len(ns) + 1):
                shadow_keys.add(".".join(ns[:i]) + "." + opened)

    has_standalone_cmd = False
    has_nonlocal = False
    cleaned, _ = strip_comments_and_extract_docstrings("\n".join(body_lines))
    for ln in cleaned.splitlines():
        if not ln or ln[0] in (" ", "\t"):
            continue
        if _STANDALONE_CMD_RE.match(ln):
            has_standalone_cmd = True
        if _NONLOCAL_ATTR_OR_INST_RE.match(ln):
            has_nonlocal = True

    is_standalone = (
        (mod_name in root_mods)
        or (mod_name in ("Main", "Statements"))
        or has_standalone_cmd
        or (not scopes_ok)
    )

    nonblank_loc = sum(1 for ln in source_text.splitlines() if ln.strip())
    lib_root = _glob_to_bucket(mod_name, lib_globs)

    return MergeUnit(
        mod_name=mod_name,
        rel_path=rel_path,
        lib_root=lib_root,
        imports=imports,
        body_lines=body_lines,
        unclosed_ends=unclosed_ends,
        nonblank_loc=nonblank_loc,
        decl_names=decl_names,
        private_names=private_names,
        is_standalone=is_standalone,
        has_nonlocal_attr_or_inst=has_nonlocal,
        dup_group_key=dup_group_key,
        declared_namespaces=frozenset(declared_ns),
        open_shadow_keys=frozenset(shadow_keys),
    )


def _common_prefix_within_lib(mod_names: Sequence[str], lib_root: str) -> str:
    """Compute longest common dotted prefix of ``mod_names`` staying inside ``lib_root``."""
    if not mod_names:
        return lib_root
    split_mods = [m.split(".")[:-1] for m in mod_names]
    if not all(split_mods):
        return lib_root
    prefix = list(split_mods[0])
    for parts in split_mods[1:]:
        k = 0
        limit = min(len(prefix), len(parts))
        while k < limit and prefix[k] == parts[k]:
            k += 1
        prefix = prefix[:k]
    joined = ".".join(prefix)
    lib_clean = lib_root.split(":")[-1] if lib_root.startswith("__root__") else lib_root
    if not joined or (len(joined) < len(lib_clean)) or not (
        joined == lib_clean or joined.startswith(lib_clean + ".")
    ):
        return lib_clean
    return joined


def _render_bundle_text(
    bundle_mod_name: str,
    units: Sequence[MergeUnit],
    mod_rename_map: dict[str, str],
    extra_imports: Sequence[str] = (),
) -> str:
    """Render a merged bundle `.lean` source file with deduplicated imports and section isolation."""
    # Preserve single-unit files minimally (rewriting imports only)
    if len(units) == 1 and bundle_mod_name == units[0].mod_name:
        u = units[0]
        seen_imp: set[str] = set()
        ext_imps: list[str] = []
        proj_imps: list[str] = []
        for imp in list(u.imports) + list(extra_imports):
            mapped = mod_rename_map.get(imp, imp)
            if mapped == bundle_mod_name or mapped in seen_imp:
                continue
            seen_imp.add(mapped)
            if mapped in mod_rename_map.values() or mapped in mod_rename_map:
                proj_imps.append(mapped)
            else:
                ext_imps.append(mapped)
        imp_lines = [f"import {x}" for x in ext_imps] + [f"import {x}" for x in proj_imps]
        parts: list[str] = []
        if imp_lines:
            parts.append("\n".join(imp_lines))
        if u.body_lines:
            parts.append("\n".join(u.body_lines))
        text = "\n\n".join(parts)
        return (text + "\n") if text else ""

    seen_imp = set()
    ext_imps = []
    proj_imps = []
    unit_orig_names = {u.mod_name for u in units}
    for u in units:
        for imp in u.imports:
            if imp in unit_orig_names:
                continue
            mapped = mod_rename_map.get(imp, imp)
            if mapped == bundle_mod_name or mapped in seen_imp:
                continue
            seen_imp.add(mapped)
            if mapped in mod_rename_map.values() or mapped in mod_rename_map:
                proj_imps.append(mapped)
            else:
                ext_imps.append(mapped)
    for imp in extra_imports:
        mapped = mod_rename_map.get(imp, imp)
        if mapped == bundle_mod_name or mapped in seen_imp:
            continue
        seen_imp.add(mapped)
        proj_imps.append(mapped)

    out_sections: list[str] = []
    imp_lines = [f"import {x}" for x in ext_imps] + [f"import {x}" for x in proj_imps]
    if imp_lines:
        out_sections.append("\n".join(imp_lines))

    for idx, u in enumerate(units):
        if not u.body_lines:
            continue
        tag = f"__pc_u_{idx}"
        block = [f"section {tag}"]
        block.extend(u.body_lines)
        block.extend(u.unclosed_ends)
        block.append(f"end {tag}")
        out_sections.append("\n".join(block))

    text = "\n\n".join(out_sections)
    return (text + "\n") if text else ""


def _compute_bundle_dag_reach(
    bundle_names: Sequence[str],
    deps_by_bundle: dict[str, set[str]],
) -> tuple[dict[str, int], dict[str, int], dict[str, int]]:
    """Compute topological rank and transitive dependency bitsets on the merged bundle DAG."""
    b_list = sorted(bundle_names)
    b_bit = {b: 1 << i for i, b in enumerate(b_list)}
    in_deg = {b: 0 for b in b_list}
    rev: dict[str, list[str]] = defaultdict(list)

    for b in b_list:
        for d in deps_by_bundle.get(b, ()):
            if d != b and d in in_deg:
                rev[d].append(b)
                in_deg[b] += 1

    q: deque[str] = deque(b for b, c in in_deg.items() if c == 0)
    topo: list[str] = []
    while q:
        u = q.popleft()
        topo.append(u)
        for p in rev[u]:
            in_deg[p] -= 1
            if in_deg[p] == 0:
                q.append(p)

    topo_rank = {b: i for i, b in enumerate(topo)}
    trans_bits = {b: 0 for b in b_list}
    for b in topo:
        bits = 0
        for d in deps_by_bundle.get(b, ()):
            if d != b and d in b_bit:
                bits |= b_bit[d] | trans_bits[d]
        trans_bits[b] = bits

    return topo_rank, b_bit, trans_bits


def _run_phase_b_consolidation(
    bundle_texts: dict[str, str],
    bundle_units: dict[str, list[MergeUnit]],
    bundle_deps: dict[str, set[str]],
    mod_rename_map: dict[str, str],
    *,
    conn: sqlite3.Connection | None,
    plan: PrunePlan | None,
    allow_cross_bundle: bool = True,
    min_saved_loc: int = 2,
) -> tuple[dict[str, str], dict[str, set[str]], tuple[int, int, int, int]]:
    """Phase B: Exact-duplicate consolidation directly over rendered merged bundles.

    Returns ``(updated_bundle_texts, updated_bundle_deps, (b1_same, b1_imp, b2_cross, saved_loc))``.
    """
    # Collect theorem/lemma declarations across all merged bundles by re-parsing rendered bundle files
    # so start_line / end_line match the exact post-transform, post-merge source!
    type_refs_by_name: dict[str, frozenset[int]] = {}
    if conn is not None and plan is not None:
        cur = conn.cursor()
        name_to_id: dict[str, int] = {}
        for did, name, mid in cur.execute(
            "SELECT id, name, module_id FROM declarations "
            "WHERE is_mathlib = 0 AND kind IN ('theorem', 'lemma')"
        ):
            if int(did) in plan.kept_decl_ids and int(mid or 0) in plan.kept_modules:
                name_to_id[name] = int(did)
        id_to_name = {v: k for k, v in name_to_id.items()}
        trefs: dict[int, set[int]] = defaultdict(set)
        if id_to_name:
            for src_id, dst_id in cur.execute("SELECT src_id, dst_id FROM edges WHERE kind = 'type'"):
                if src_id in id_to_name:
                    trefs[src_id].add(dst_id)
            for did, nm in id_to_name.items():
                type_refs_by_name[nm] = frozenset(trefs.get(did, ()))

    # Parse all non-standalone bundles (and standalone ones) for theorem/lemma locations
    parsed_decls_by_hash: dict[str, list[dict[str, Any]]] = defaultdict(list)
    bundle_has_nonlocal = {
        b: any(u.has_nonlocal_attr_or_inst or u.is_standalone for u in us)
        for b, us in bundle_units.items()
    }

    for bname, btxt in bundle_texts.items():
        pmod = parse_lean_source(btxt, bname)
        for d in pmod.declarations:
            if d.kind not in ("theorem", "lemma") or not d.canonical_type_hash:
                continue
            if d.is_private:
                continue
            ph = parse_signature_structure(d.type_sig)
            if ph is None:
                continue
            if type_refs_by_name and d.name not in type_refs_by_name:
                # Without resolved type refs, equal header text under different `open`s
                # (`exp` from Real vs Complex) would be grouped as duplicates.
                continue
            tref_key = (
                type_refs_by_name.get(d.name, frozenset())
                if type_refs_by_name
                else frozenset(d.type_refs)
            )
            parsed_decls_by_hash[d.canonical_type_hash].append(
                {
                    "name": d.name,
                    "short_name": d.short_name,
                    "bundle": bname,
                    "start_line": d.start_line,
                    "end_line": d.end_line,
                    "body_loc": d.body_loc,
                    "type_sig": d.type_sig,
                    "parsed_header": ph,
                    "tref_key": tref_key,
                    "structural_key": ph.structural_key,
                }
            )

    # Group by exact (canonical_type_hash, type_refs, structural_key)
    exact_groups: dict[tuple[str, Any, Any], list[dict[str, Any]]] = defaultdict(list)
    for h, items in parsed_decls_by_hash.items():
        if len(items) < 2:
            continue
        for it in items:
            exact_groups[(h, it["tref_key"], it["structural_key"])].append(it)

    topo_rank, b_bit, trans_bits = _compute_bundle_dag_reach(
        list(bundle_texts.keys()),
        bundle_deps,
    )

    ops_by_bundle: dict[str, list[tuple[ConsolidationOp, str | None]]] = defaultdict(list)
    ctx_cache: dict[tuple[str, int, int], Any] = {}

    def _get_ctx(bname: str, sl: int, el: int) -> Any:
        key = (bname, sl, el)
        if key not in ctx_cache:
            ctx_cache[key] = _extract_decl_source_context(bundle_texts[bname], sl, el)
        return ctx_cache[key]

    b1_same = 0
    b1_imp = 0
    b2_cross = 0

    for g in exact_groups.values():
        if len(g) < 2:
            continue
        g.sort(key=lambda d: (topo_rank.get(d["bundle"], 10**9), d["start_line"], d["name"]))

        # Track root canonical per index so we never form delegation chains
        delegated_root: dict[int, int] = {}

        for i in range(1, len(g)):
            di = g[i]
            if not di["parsed_header"].safe_for_delegation:
                continue
            d_ctx = _get_ctx(di["bundle"], di["start_line"], di["end_line"])
            if d_ctx is None or d_ctx.is_private or d_ctx.is_unsafe_modifier or d_ctx.in_mutual:
                continue
            if d_ctx.has_explicit_section_var or d_ctx.body_has_structural_line:
                continue
            if d_ctx.parsed_header is None or not d_ctx.parsed_header.safe_for_delegation:
                continue
            actual_saved = d_ctx.proof_body_nonblank_lines - 1
            if actual_saved < min_saved_loc:
                continue

            db = di["bundle"]
            db_trans = trans_bits.get(db, 0)

            # Prefer Tier B1 (same-bundle -> imported-bundle) before Tier B2 (acyclic cross-bundle)
            chosen_c: dict[str, Any] | None = None
            chosen_tier: str | None = None
            extra_imp: str | None = None

            for pass_tier in ("same", "imported", "cross"):
                if pass_tier == "cross" and not allow_cross_bundle:
                    continue
                for j in range(i):
                    root_j = delegated_root.get(j, j)
                    ci = g[root_j]
                    cb = ci["bundle"]

                    if pass_tier == "same":
                        if not (cb == db and ci["start_line"] < di["start_line"]):
                            continue
                    elif pass_tier == "imported":
                        if not (cb != db and (db_trans & b_bit.get(cb, 0))):
                            continue
                    else:  # cross-bundle acyclic
                        if cb == db or (db_trans & b_bit.get(cb, 0)):
                            continue
                        if topo_rank.get(cb, 10**9) >= topo_rank.get(db, -1):
                            continue
                        if bundle_has_nonlocal.get(cb, True):
                            continue

                    c_ctx = _get_ctx(cb, ci["start_line"], ci["end_line"])
                    if c_ctx is None or c_ctx.is_private or c_ctx.is_unsafe_modifier or c_ctx.in_mutual:
                        continue
                    if c_ctx.has_explicit_section_var or c_ctx.parsed_header is None:
                        continue
                    if c_ctx.parsed_header.structural_key != d_ctx.parsed_header.structural_key:
                        continue
                    if c_ctx.universe_params != d_ctx.universe_params:
                        continue
                    if c_ctx.active_implicit_vars != d_ctx.active_implicit_vars:
                        continue

                    chosen_c = ci
                    chosen_tier = pass_tier
                    delegated_root[i] = root_j
                    if pass_tier == "cross":
                        extra_imp = cb
                    break
                if chosen_c is not None:
                    break

            if chosen_c is None or chosen_tier is None:
                continue

            rhs = build_delegation_rhs(f"_root_.{chosen_c['name']}", d_ctx.parsed_header)
            op = ConsolidationOp(
                dup_decl_id=0,
                dup_name=di["name"],
                dup_short_name=di["short_name"],
                dup_module_id=0,
                dup_module_path=db,
                dup_start_line=di["start_line"],
                dup_end_line=di["end_line"],
                dup_body_loc=di["body_loc"],
                canon_decl_id=0,
                canon_name=chosen_c["name"],
                canon_short_name=chosen_c["short_name"],
                canon_module_id=0,
                canon_module_path=chosen_c["bundle"],
                canon_start_line=chosen_c["start_line"],
                canon_end_line=chosen_c["end_line"],
                same_module=(chosen_tier == "same"),
                delegation_rhs=rhs,
                estimated_saved_loc=actual_saved,
                verified=True,
            )
            ops_by_bundle[db].append((op, extra_imp))
            if chosen_tier == "same":
                b1_same += 1
            elif chosen_tier == "imported":
                b1_imp += 1
            else:
                b2_cross += 1

    # Apply consolidation edits and inject any cross-bundle imports
    total_saved_loc = 0
    for bname, op_pairs in ops_by_bundle.items():
        lines = bundle_texts[bname].splitlines()
        ops = [op for op, _ in op_pairs]
        new_lines, applied, saved = apply_consolidations_to_lines(lines, ops)
        if applied <= 0:
            continue
        total_saved_loc += saved

        extra_imps_for_b = sorted({imp for _, imp in op_pairs if imp is not None})
        if extra_imps_for_b:
            existing_imps = set(bundle_deps.get(bname, ()))
            to_insert = [imp for imp in extra_imps_for_b if imp not in existing_imps and imp != bname]
            if to_insert:
                bundle_deps[bname].update(to_insert)
                # Insert right after last leading import line (or at line 0)
                insert_pos = 0
                for idx, ln in enumerate(new_lines):
                    if _IMPORT_LINE_RE.match(ln):
                        insert_pos = idx + 1
                    elif ln.strip() and not ln.strip().startswith("--"):
                        break
                imp_insert_lines = [f"import {x}" for x in to_insert]
                new_lines = new_lines[:insert_pos] + imp_insert_lines + new_lines[insert_pos:]

        new_text = "\n".join(new_lines)
        if bundle_texts[bname].endswith("\n"):
            new_text += "\n"
        bundle_texts[bname] = new_text

    return bundle_texts, bundle_deps, (b1_same, b1_imp, b2_cross, total_saved_loc)


# ---------------------------------------------------------------------------
# Main Phase A + Phase B orchestrator
# ---------------------------------------------------------------------------


def merge_project_modules(
    module_sources: dict[str, tuple[str, str]],
    *,
    target_module_loc: int = 1400,
    lakefile_toml_text: str | None = None,
    root_modules: Sequence[str] = ("Main", "Statements"),
    conn: sqlite3.Connection | None = None,
    plan: PrunePlan | None = None,
    consolidate_duplicates: bool = True,
    allow_cross_bundle_consolidation: bool = True,
) -> tuple[dict[str, tuple[str, str]], MergeReport]:
    """Merge a dictionary of kept modules into cycle-free topological bundles.

    Parameters
    ----------
    module_sources:
        Mapping ``mod_name -> (rel_path, source_text)`` for all kept ``.lean`` files.
    target_module_loc:
        Maximum non-blank LOC target per merged bundle.
    lakefile_toml_text:
        Optional ``lakefile.toml`` text used to respect ``[[lean_lib]]`` glob boundaries.
    root_modules:
        Modules kept unmerged as entrypoints (e.g. ``Main``, ``Statements``).
    conn, plan:
        Optional DB connection and ``PrunePlan`` for DB-backed type-edge duplicate grouping.
    consolidate_duplicates:
        When True, run Phase B exact-duplicate consolidation on the merged bundles.
    allow_cross_bundle_consolidation:
        When True, permit cycle-free cross-bundle delegation (``topo_rank(C) < topo_rank(D)``)
        when the canonical bundle has no nonlocal ``attribute``/``instance`` declarations.

    Returns
    -------
    ``(merged_files_by_mod_name, MergeReport)`` where ``merged_files_by_mod_name`` maps
    ``bundle_mod_name -> (rel_path, rendered_source)``.
    """
    lib_globs = parse_lakefile_lib_globs(lakefile_toml_text)
    root_set = set(root_modules)

    # Optional DB duplicate-group hint for co-locating duplicate-sharing siblings in Phase A2
    mod_dup_hint: dict[str, int] = {}
    if conn is not None and plan is not None:
        cur = conn.cursor()
        by_hash_mods: dict[str, list[str]] = defaultdict(list)
        for did, mid, _kind, h in cur.execute(
            "SELECT id, module_id, kind, canonical_type_hash FROM declarations "
            "WHERE is_mathlib = 0 AND kind IN ('theorem', 'lemma') "
            "AND canonical_type_hash IS NOT NULL AND canonical_type_hash != ''"
        ):
            if int(did) in plan.kept_decl_ids and int(mid or 0) in plan.kept_modules:
                by_hash_mods[h].append(plan.mod_path[int(mid)])
        for gi, (_, mnames) in enumerate(by_hash_mods.items()):
            if len(mnames) >= 2:
                for mn in mnames:
                    mod_dup_hint.setdefault(mn, gi)

    units: dict[str, MergeUnit] = {}
    input_imp_lines = 0
    input_nonblank = 0
    for mod_name, (rel_path, src) in module_sources.items():
        u = _analyze_unit(
            mod_name,
            rel_path,
            src,
            lib_globs=lib_globs,
            root_mods=root_set,
            dup_group_key=mod_dup_hint.get(mod_name),
        )
        units[mod_name] = u
        input_imp_lines += len(u.imports)
        input_nonblank += u.nonblank_loc

    kept_set = set(units.keys())
    standalone_count = sum(1 for u in units.values() if u.is_standalone)

    # Quotient union-find state
    parent = {m: m for m in kept_set}
    b_loc = {m: u.nonblank_loc for m, u in units.items()}
    b_members: dict[str, list[str]] = {m: [m] for m in kept_set}
    b_decls = {m: set(u.decl_names) for m, u in units.items()}
    b_privs = {m: set(u.private_names) for m, u in units.items()}
    b_ns = {m: set(u.declared_namespaces) for m, u in units.items()}
    b_shadow = {m: set(u.open_shadow_keys) for m, u in units.items()}

    def _shadow_conflict(x: str, y: str) -> bool:
        """True if merging bundles `x` and `y` would let one hijack the other's `open`s."""
        return not (b_shadow[x].isdisjoint(b_ns[y]) and b_shadow[y].isdisjoint(b_ns[x]))

    def _absorb_scope_sets(dst: str, src: str) -> None:
        b_ns[dst] |= b_ns[src]
        b_shadow[dst] |= b_shadow[src]
        b_ns[src].clear()
        b_shadow[src].clear()
    b_standalone = {m: u.is_standalone for m, u in units.items()}
    b_lib = {m: u.lib_root for m, u in units.items()}

    b_deps: dict[str, set[str]] = {
        m: {imp for imp in u.imports if imp in kept_set and imp != m}
        for m, u in units.items()
    }
    b_rdeps: dict[str, set[str]] = defaultdict(set)
    for m, ds in b_deps.items():
        for d in ds:
            b_rdeps[d].add(m)

    def _find(x: str) -> str:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def _run_chain_fusion() -> int:
        fused = 0
        changed = True
        while changed:
            changed = False
            for child in list(kept_set):
                rc = _find(child)
                if rc != child or b_standalone[rc]:
                    continue
                if len(b_rdeps[rc]) != 1:
                    continue
                rp = _find(next(iter(b_rdeps[rc])))
                if rp == rc or b_standalone[rp]:
                    continue
                if b_lib[rc] != b_lib[rp]:
                    continue
                if b_loc[rc] + b_loc[rp] > target_module_loc:
                    continue
                if not b_decls[rc].isdisjoint(b_decls[rp]):
                    continue
                if not b_privs[rc].isdisjoint(b_privs[rp]):
                    continue
                if _shadow_conflict(rc, rp):
                    continue

                # Fuse child `rc` BEFORE consumer `rp`
                parent[rc] = rp
                b_loc[rp] += b_loc[rc]
                b_members[rp] = b_members[rc] + b_members[rp]
                b_decls[rp] |= b_decls[rc]
                b_privs[rp] |= b_privs[rc]
                _absorb_scope_sets(rp, rc)
                b_deps[rp].discard(rc)
                for d in b_deps[rc]:
                    rd = _find(d)
                    if rd != rp:
                        b_deps[rp].add(rd)
                        b_rdeps[rd].discard(rc)
                        b_rdeps[rd].add(rp)
                b_deps[rc].clear()
                b_rdeps[rc].clear()
                b_members[rc] = []
                b_decls[rc].clear()
                b_privs[rc].clear()
                fused += 1
                changed = True
        return fused

    # Phase A1: Single-consumer chain fusion
    a1_fused = _run_chain_fusion()
    active_a1 = {_find(m) for m in kept_set}

    # Compute exact topological layers on the A1 quotient DAG
    in_deg = {b: len({d for d in b_deps[b] if _find(d) != b}) for b in active_a1}
    q: deque[str] = deque(b for b, c in in_deg.items() if c == 0)
    layer: dict[str, int] = {}
    while q:
        u = q.popleft()
        layer[u] = 1 + max((layer[_find(d)] for d in b_deps[u] if _find(d) != u), default=-1)
        for p in b_rdeps[u]:
            rp = _find(p)
            if rp in active_a1:
                in_deg[rp] -= 1
                if in_deg[rp] == 0:
                    q.append(rp)

    max_layer = max(layer.values(), default=0)

    # Phase A2: Duplicate-aware convex antichain packing within `(lib_root, layer)`
    buckets: dict[tuple[str, int], list[str]] = defaultdict(list)
    for b in active_a1:
        if not b_standalone[b]:
            buckets[(b_lib[b], layer.get(b, 0))].append(b)

    def _bucket_sort_key(b: str) -> tuple[int, int, str, str]:
        hints = [units[m].dup_group_key for m in b_members[b] if units[m].dup_group_key is not None]
        pdir = b.rsplit(".", 1)[0] if "." in b else ""
        return (0 if hints else 1, min(hints) if hints else 10**9, pdir, b)

    for (_, _), bs in buckets.items():
        bs.sort(key=_bucket_sort_key)
        rep_b: str | None = None
        for b in bs:
            if (
                rep_b is None
                or b_loc[rep_b] + b_loc[b] > target_module_loc
                or not b_decls[rep_b].isdisjoint(b_decls[b])
                or not b_privs[rep_b].isdisjoint(b_privs[b])
                or _shadow_conflict(rep_b, b)
            ):
                rep_b = b
                continue
            parent[b] = rep_b
            b_loc[rep_b] += b_loc[b]
            b_members[rep_b].extend(b_members[b])
            b_decls[rep_b] |= b_decls[b]
            b_privs[rep_b] |= b_privs[b]
            _absorb_scope_sets(rep_b, b)
            for d in b_deps[b]:
                rd = _find(d)
                if rd != rep_b:
                    b_deps[rep_b].add(rd)
                    b_rdeps[rd].discard(b)
                    b_rdeps[rd].add(rep_b)
            for p in b_rdeps[b]:
                rp = _find(p)
                if rp != rep_b:
                    b_rdeps[rep_b].add(rp)
                    b_deps[rp].discard(b)
                    b_deps[rp].add(rep_b)
            b_deps[b].clear()
            b_rdeps[b].clear()
            b_members[b] = []
            b_decls[b].clear()
            b_privs[b].clear()

    active_a2 = {_find(m) for m in kept_set}

    # Phase A3: Second-pass single-consumer chain fusion on A2 quotient DAG
    a3_fused = _run_chain_fusion()
    final_reps = sorted({_find(m) for m in kept_set})

    # Assign collision-free final bundle module names and paths
    existing_all = set(kept_set)
    bundle_name_by_rep: dict[str, str] = {}
    used_bundle_names: set[str] = set()

    bundle_counter = 0
    for rep in final_reps:
        members = b_members[rep]
        if len(members) == 1:
            bname = members[0]
        else:
            common = _common_prefix_within_lib(members, b_lib[rep])
            while True:
                cand = f"{common}.PCBundle_{bundle_counter:05d}"
                bundle_counter += 1
                if cand not in existing_all and cand not in used_bundle_names:
                    bname = cand
                    break
        bundle_name_by_rep[rep] = bname
        used_bundle_names.add(bname)

    mod_rename_map: dict[str, str] = {}
    bundle_units: dict[str, list[MergeUnit]] = {}
    bundle_deps: dict[str, set[str]] = {}

    for rep in final_reps:
        bname = bundle_name_by_rep[rep]
        members = b_members[rep]
        bundle_units[bname] = [units[m] for m in members]
        for m in members:
            mod_rename_map[m] = bname

    for rep in final_reps:
        bname = bundle_name_by_rep[rep]
        deps: set[str] = set()
        for d in b_deps[rep]:
            db = bundle_name_by_rep[_find(d)]
            if db != bname:
                deps.add(db)
        bundle_deps[bname] = deps

    # Render initial merged bundle texts
    bundle_texts: dict[str, str] = {
        bname: _render_bundle_text(bname, us, mod_rename_map)
        for bname, us in bundle_units.items()
    }

    # Phase B: Post-merge exact-duplicate consolidation
    b1_same = b1_imp = b2_cross = b_saved_loc = 0
    if consolidate_duplicates:
        bundle_texts, bundle_deps, (b1_same, b1_imp, b2_cross, b_saved_loc) = (
            _run_phase_b_consolidation(
                bundle_texts,
                bundle_units,
                bundle_deps,
                mod_rename_map,
                conn=conn,
                plan=plan,
                allow_cross_bundle=allow_cross_bundle_consolidation,
            )
        )

    # Verify 0 cycles and 0 dangling project imports in final bundle DAG
    final_names = set(bundle_texts.keys())
    in_deg_f = {b: len(bundle_deps[b] & final_names) for b in final_names}
    rev_f: dict[str, list[str]] = defaultdict(list)
    for b in final_names:
        for d in bundle_deps[b] & final_names:
            rev_f[d].append(b)
    qf: deque[str] = deque(b for b, c in in_deg_f.items() if c == 0)
    topo_f = 0
    while qf:
        u = qf.popleft()
        topo_f += 1
        for p in rev_f[u]:
            in_deg_f[p] -= 1
            if in_deg_f[p] == 0:
                qf.append(p)
    cycle_count = len(final_names) - topo_f

    dangling_imports = 0
    out_imp_lines = 0
    out_nonblank = 0
    out_total_lines = 0
    bundle_locs: list[int] = []
    merged_files: dict[str, tuple[str, str]] = {}

    # Keep each bundle under its members' source root (`src/`, ``, `Proj/`...) so lake's
    # srcDir still finds it; default to `src/` when no member path reveals the root.
    bundle_root: dict[str, str] = {}
    for mod_name, (orig_rel, _src) in module_sources.items():
        suffix = mod_name.replace(".", "/") + ".lean"
        if orig_rel.endswith(suffix):
            bundle_root.setdefault(mod_rename_map.get(mod_name, mod_name), orig_rel[: -len(suffix)])

    for bname, btxt in bundle_texts.items():
        lns = btxt.splitlines()
        nb = sum(1 for l in lns if l.strip())
        out_nonblank += nb
        out_total_lines += len(lns)
        bundle_locs.append(nb)
        for l in lns:
            mm = _IMPORT_LINE_RE.match(l)
            if mm:
                out_imp_lines += 1
                imp = mm.group(1)
                if imp in mod_rename_map and imp not in final_names:
                    dangling_imports += 1
        rel_path = f"{bundle_root.get(bname, 'src/')}{bname.replace('.', '/')}.lean"
        merged_files[bname] = (rel_path, btxt)

    in_cnt = len(module_sources)
    out_cnt = len(merged_files)
    red_pct = round(100.0 * (in_cnt - out_cnt) / in_cnt, 2) if in_cnt > 0 else 0.0

    report = MergeReport(
        target_module_loc=target_module_loc,
        input_modules=in_cnt,
        standalone_modules=standalone_count,
        phase_a1_fused_modules=a1_fused,
        after_phase_a1_modules=len(active_a1),
        after_phase_a2_modules=len(active_a2),
        phase_a3_fused_modules=a3_fused,
        output_modules=out_cnt,
        module_reduction_pct=red_pct,
        input_nonblank_loc=input_nonblank,
        output_nonblank_loc=out_nonblank,
        output_total_lines=out_total_lines,
        loc_saved_by_merge=max(0, input_nonblank - out_nonblank),
        input_import_lines=input_imp_lines,
        output_import_lines=out_imp_lines,
        eliminated_import_lines=max(0, input_imp_lines - out_imp_lines),
        max_bundle_loc=max(bundle_locs, default=0),
        mean_bundle_loc=round(sum(bundle_locs) / len(bundle_locs), 1) if bundle_locs else 0.0,
        max_dag_layer=max_layer,
        dangling_imports=dangling_imports,
        cycle_count=cycle_count,
        phase_b_same_bundle_consolidations=b1_same,
        phase_b_imported_bundle_consolidations=b1_imp,
        phase_b_cross_bundle_consolidations=b2_cross,
        phase_b_total_consolidations=b1_same + b1_imp + b2_cross,
        phase_b_saved_loc=b_saved_loc,
    )
    return merged_files, report
