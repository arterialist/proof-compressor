"""Pass 1: Safe exact-duplicate proof consolidation for Lean 4 repositories.

Scans kept non-instance/non-class ``theorem``/``lemma`` declarations grouped by
exact ``canonical_type_hash``, resolved type-level dependency edges, and exact
binder/return-type structure.

Two consolidation levels are computed:
1. **Conservative in-scope consolidation (zero new imports)**:
   A duplicate declaration ``D`` delegates its multi-line proof body to a single
   canonical representative ``C`` that is ALREADY defined strictly earlier in
   the same module or strictly earlier in ``D``'s kept transitive import closure.
   Every applied delegation is further verified against actual Lean 4 source
   context (no ``private`` cross-module targets, no ``let``/``letI`` signature
   truncation, no explicit section ``variable (...)`` mismatches, matching
   implicit/instance ``variable`` context, matching binder kinds, and inferable
   implicit arguments).
2. **Hoisted shared-module consolidation potential** (``Consolidated.SharedLemmas``):
   Quantifies the additional exact-duplicate reduction achievable by hoisting
   cross-branch exact-type duplicates into a shared canonical module.
"""

from __future__ import annotations

import re
import sqlite3
from collections import defaultdict, deque
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any, Iterable

from proof_compressor.ingest.lean_parser import (
    canonicalize_type,
    strip_comments_and_extract_docstrings,
)
from proof_compressor.schema import connect_db

if TYPE_CHECKING:
    from proof_compressor.analyze.materialize import PrunePlan


_IDENT_START_CHARS = r"A-Za-z_\u00c0-\u024f\u0370-\u03ff\u1e00-\u1eff\u2100-\u214f"
_IDENT_CONT_CHARS = r"A-Za-z0-9_'\u0080-\uffff"

_UNSAFE_TYPE_SIG_RE = re.compile(r"\b(?:let|letI|have|haveI|match|where|sorry|admit)\b")
_IDENT_SIMPLE_RE = re.compile(rf"^[{_IDENT_START_CHARS}][{_IDENT_CONT_CHARS}]*$")
_DECL_MOD_HEADER_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|public|noncomputable|partial|unsafe|meta|scoped|local)\s+)*"
    r"(theorem|lemma)\b(.*)$",
    re.DOTALL,
)
_DECL_NAME_RE = re.compile(
    rf"^(?:«([^»]+)»|([{_IDENT_START_CHARS}][{_IDENT_CONT_CHARS}]*(?:\.[{_IDENT_START_CHARS}][{_IDENT_CONT_CHARS}]*)*))"
)
_STRUCTURAL_BODY_LINE_RE = re.compile(
    r"^(?:namespace|section|noncomputable\s+section|end|open|variable|variables|"
    r"universe|universes|import|mutual|theorem|lemma|def|abbrev|structure|class|"
    r"inductive|instance|axiom|opaque|constant)\b"
)
_UNIVERSE_DECL_RE = re.compile(r"^universes?\s+(.*)$")
_VARIABLE_DECL_RE = re.compile(r"^variables?\s+(.*)$")
_NAMESPACE_LINE_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*)")
_SECTION_LINE_RE = re.compile(
    r"^(?:noncomputable\s+)?section(?:\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*))?\b"
)
_END_LINE_RE = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*))?\s*$")
_MUTUAL_LINE_RE = re.compile(r"^mutual\s*$")
_WORD_RE = re.compile(rf"[{_IDENT_START_CHARS}][{_IDENT_CONT_CHARS}]*")
_TYPE_STAR_RE = re.compile(r"\bType\s*\*")


@dataclass(frozen=True)
class BinderEntry:
    """Single flattened binder from a Lean 4 theorem header or ``variable`` command."""

    bracket: str  # '(', '{', '[', '⦃'
    var_name: str | None  # None for anonymous instance binder `[CommRing R]`
    type_expr: str


@dataclass(frozen=True)
class ParsedHeader:
    """Structured parse of a Lean 4 theorem/lemma signature."""

    binders: tuple[BinderEntry, ...]
    ret_type: str
    structural_key: tuple[tuple[tuple[str, str], ...], str]
    explicit_vars: tuple[str, ...]
    implicit_vars: tuple[str, ...]
    safe_for_delegation: bool


@dataclass
class ConsolidationOp:
    """Single planned/verified in-scope exact-duplicate proof delegation."""

    dup_decl_id: int
    dup_name: str
    dup_short_name: str
    dup_module_id: int
    dup_module_path: str
    dup_start_line: int
    dup_end_line: int
    dup_body_loc: int

    canon_decl_id: int
    canon_name: str
    canon_short_name: str
    canon_module_id: int
    canon_module_path: str
    canon_start_line: int
    canon_end_line: int

    same_module: bool
    delegation_rhs: str
    estimated_saved_loc: int
    verified: bool = False

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ConsolidationReport:
    """Quantitative summary of in-scope and hoisted exact-duplicate consolidation."""

    analyzed_kept_theorems: int = 0
    exact_hash_groups: int = 0
    exact_verified_groups: int = 0

    in_scope_candidates: int = 0
    in_scope_same_module: int = 0
    in_scope_imported: int = 0
    in_scope_estimated_saved_loc: int = 0

    source_verified_ops: int = 0
    source_skipped_ops: int = 0
    applied_consolidations: int = 0
    applied_saved_loc: int = 0

    hoistable_groups: int = 0
    hoistable_redundant_decls: int = 0
    hoistable_estimated_saved_loc: int = 0
    hoist_target_module: str = "Consolidated.SharedLemmas"

    top_in_scope_ops: list[dict[str, Any]] = field(default_factory=list)
    top_hoistable_groups: list[dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ConsolidationPlan:
    """Planned exact-duplicate delegations indexed by module ID."""

    ops_by_mod: dict[int, list[ConsolidationOp]] = field(default_factory=dict)
    canon_mods_needed: set[int] = field(default_factory=set)
    dup_mods_needed: set[int] = field(default_factory=set)
    report: ConsolidationReport = field(default_factory=ConsolidationReport)


# ---------------------------------------------------------------------------
# Low-level Lean 4 signature & binder parsing
# ---------------------------------------------------------------------------


def _match_close_bracket(ch: str) -> str:
    return {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}[ch]


def _find_top_level_colon(text: str) -> int:
    """Return index of the first top-level single ``:`` (not ``:=`` or ``::``), or -1."""
    depth_p = depth_b = depth_c = depth_g = 0
    in_str = False
    n = len(text)
    i = 0
    while i < n:
        ch = text[i]
        if in_str:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
            i += 1
            continue
        if ch == "(":
            depth_p += 1
        elif ch == ")" and depth_p > 0:
            depth_p -= 1
        elif ch == "[":
            depth_b += 1
        elif ch == "]" and depth_b > 0:
            depth_b -= 1
        elif ch in ("{", "⦃"):
            depth_c += 1
        elif ch in ("}", "⦄") and depth_c > 0:
            depth_c -= 1
        elif ch == "«":
            depth_g += 1
        elif ch == "»" and depth_g > 0:
            depth_g -= 1
        elif depth_p == 0 and depth_b == 0 and depth_c == 0 and depth_g == 0 and ch == ":":
            next_ch = text[i + 1] if i + 1 < n else ""
            prev_ch = text[i - 1] if i > 0 else ""
            if next_ch not in (":", "=") and prev_ch != ":":
                return i
        i += 1
    return -1


def find_top_level_assign(text: str) -> int:
    """Return index of the first top-level ``:=`` outside brackets/strings, or -1."""
    depth_p = depth_b = depth_c = depth_g = 0
    in_str = False
    n = len(text)
    i = 0
    while i < n:
        ch = text[i]
        if in_str:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
            i += 1
            continue
        if ch == "(":
            depth_p += 1
        elif ch == ")" and depth_p > 0:
            depth_p -= 1
        elif ch == "[":
            depth_b += 1
        elif ch == "]" and depth_b > 0:
            depth_b -= 1
        elif ch in ("{", "⦃"):
            depth_c += 1
        elif ch in ("}", "⦄") and depth_c > 0:
            depth_c -= 1
        elif ch == "«":
            depth_g += 1
        elif ch == "»" and depth_g > 0:
            depth_g -= 1
        elif (
            depth_p == 0
            and depth_b == 0
            and depth_c == 0
            and depth_g == 0
            and ch == ":"
            and i + 1 < n
            and text[i + 1] == "="
        ):
            return i
        i += 1
    return -1


def parse_binder_list(binders_str: str) -> list[BinderEntry] | None:
    """Parse a sequence of Lean 4 binder groups ``(x y : T) {a : U} [Inst]``.

    Returns ``None`` if the text contains default/auto-params (``:=``),
    destructuring patterns, anonymous explicit binders (``_``), or unparseable syntax.
    """
    s = binders_str.strip()
    if not s:
        return []

    out: list[BinderEntry] = []
    n = len(s)
    i = 0
    while i < n:
        while i < n and s[i].isspace():
            i += 1
        if i >= n:
            break
        open_ch = s[i]
        if open_ch not in ("(", "{", "[", "⦃"):
            return None
        close_ch = _match_close_bracket(open_ch)

        depth = 0
        in_str = False
        j = i
        end_idx = -1
        while j < n:
            ch = s[j]
            if in_str:
                if ch == "\\" and j + 1 < n:
                    j += 2
                    continue
                if ch == '"':
                    in_str = False
                j += 1
                continue
            if ch == '"':
                in_str = True
                j += 1
                continue
            if ch == open_ch:
                depth += 1
            elif ch == close_ch:
                depth -= 1
                if depth == 0:
                    end_idx = j
                    break
            j += 1
        if end_idx == -1:
            return None

        inner = s[i + 1 : end_idx].strip()
        i = end_idx + 1
        if not inner:
            return None
        # Reject default arguments or auto-params inside binders
        if ":=" in inner:
            return None

        colon = _find_top_level_colon(inner)
        if colon == -1:
            if open_ch == "[":
                out.append(BinderEntry(bracket="[", var_name=None, type_expr=inner))
                continue
            # Untyped binder like `{x}` or `(x)` — conservative reject
            return None

        lhs = inner[:colon].strip()
        rhs = inner[colon + 1 :].strip()
        if not lhs or not rhs:
            return None

        var_tokens = lhs.split()
        for v in var_tokens:
            if v == "_":
                if open_ch == "(":
                    # Anonymous explicit hypothesis cannot be referenced by name
                    return None
                out.append(BinderEntry(bracket=open_ch, var_name=None, type_expr=rhs))
                continue
            if not _IDENT_SIMPLE_RE.match(v):
                return None
            out.append(BinderEntry(bracket=open_ch, var_name=v, type_expr=rhs))

    return out


def parse_signature_structure(type_sig: str) -> ParsedHeader | None:
    """Parse a Lean 4 theorem/lemma signature into canonical binder + return structure."""
    if not type_sig:
        return None
    cleaned = " ".join(type_sig.split()).strip()
    if not cleaned:
        return None
    if _UNSAFE_TYPE_SIG_RE.search(cleaned):
        return None
    if _TYPE_STAR_RE.search(cleaned):
        # `Type*` introduces fresh anonymous universe params per decl
        return None

    colon = _find_top_level_colon(cleaned)
    if colon == -1:
        return None

    binders_raw = cleaned[:colon].strip()
    ret_raw = cleaned[colon + 1 :].strip()
    if not ret_raw:
        return None

    binders = parse_binder_list(binders_raw)
    if binders is None:
        return None

    # Alpha-normalize binder names consistently across binders and return type
    var_map: dict[str, str] = {}
    idx = 0
    explicit_vars: list[str] = []
    implicit_vars: list[str] = []

    def _subst_vars(expr: str) -> str:
        if not var_map:
            return canonicalize_type(expr)
        replaced = re.sub(
            rf"(?<![A-Za-z0-9_'\.])([{_IDENT_START_CHARS}][{_IDENT_CONT_CHARS}]*)(?![A-Za-z0-9_'])",
            lambda m: var_map.get(m.group(1), m.group(1)),
            expr,
        )
        return canonicalize_type(replaced)

    canon_binders: list[tuple[str, str]] = []
    for b in binders:
        canon_ty = _subst_vars(b.type_expr)
        canon_binders.append((b.bracket, canon_ty))
        if b.var_name is not None:
            if b.var_name not in var_map:
                var_map[b.var_name] = f"__b{idx}"
                idx += 1
            if b.bracket == "(":
                explicit_vars.append(b.var_name)
            elif b.bracket in ("{", "⦃"):
                implicit_vars.append(b.var_name)

    canon_ret = _subst_vars(ret_raw)

    # Verify every implicit variable appears in a later explicit binder type or in ret_raw,
    # so Lean 4 can infer it unambiguously from `_root_.C <explicit_vars>`.
    safe = True
    if implicit_vars:
        # Collect words appearing in all explicit binder types + return type
        infer_pool: set[str] = set(_WORD_RE.findall(ret_raw))
        for b in binders:
            if b.bracket == "(":
                infer_pool.update(_WORD_RE.findall(b.type_expr))
        for iv in implicit_vars:
            if iv not in infer_pool:
                safe = False
                break

    return ParsedHeader(
        binders=tuple(binders),
        ret_type=ret_raw,
        structural_key=(tuple(canon_binders), canon_ret),
        explicit_vars=tuple(explicit_vars),
        implicit_vars=tuple(implicit_vars),
        safe_for_delegation=safe,
    )


def build_delegation_rhs(
    canon_ref: str,
    header: ParsedHeader,
) -> str:
    """Build a 1-line Lean 4 proof term delegating to ``canon_ref``."""
    if not header.explicit_vars:
        return canon_ref
    return f"{canon_ref} " + " ".join(header.explicit_vars)


# ---------------------------------------------------------------------------
# Phase 1: DB-level consolidation planning + hoisting measurement
# ---------------------------------------------------------------------------


def _open_db(db: sqlite3.Connection | str | Path) -> tuple[sqlite3.Connection, bool]:
    if isinstance(db, sqlite3.Connection):
        return db, False
    return connect_db(db), True


def _compute_kept_import_dag(
    kept_modules: set[int],
    mod_imports: dict[int, list[int]],
    collapsed_barrels: set[int] | None = None,
) -> tuple[dict[int, int], dict[int, int], dict[int, int]]:
    """Compute topological ranks and transitive import bitsets over ``kept_modules``.

    Follows imports through ``collapsed_barrels`` (whose live imports are spliced
    directly into callers during materialization).

    Returns ``(topo_rank, mid_to_bit, trans_bits)`` where bit ``mid_to_bit[c]`` is set
    in ``trans_bits[d]`` iff module ``c`` is strictly in ``d``'s kept transitive import closure.
    """
    mid_list = sorted(kept_modules)
    mid_to_bit = {m: 1 << i for i, m in enumerate(mid_list)}
    collapsed = collapsed_barrels or set()

    kept_imp: dict[int, list[int]] = {}
    for m in mid_list:
        direct_kept: list[int] = []
        seen_nb: set[int] = {m}
        q_b: deque[int] = deque()
        for nb in mod_imports.get(m, ()):
            if nb in seen_nb:
                continue
            seen_nb.add(nb)
            if nb in kept_modules:
                direct_kept.append(nb)
            elif nb in collapsed:
                q_b.append(nb)
        while q_b:
            b = q_b.popleft()
            for bnb in mod_imports.get(b, ()):
                if bnb in seen_nb:
                    continue
                seen_nb.add(bnb)
                if bnb in kept_modules:
                    direct_kept.append(bnb)
                elif bnb in collapsed:
                    q_b.append(bnb)
        kept_imp[m] = direct_kept

    in_deg = {m: 0 for m in mid_list}
    rev_imp: dict[int, list[int]] = defaultdict(list)
    for m in mid_list:
        for nb in kept_imp[m]:
            rev_imp[nb].append(m)
            in_deg[m] += 1

    q: deque[int] = deque(m for m in mid_list if in_deg[m] == 0)
    order: list[int] = []
    while q:
        u = q.popleft()
        order.append(u)
        for parent in rev_imp[u]:
            in_deg[parent] -= 1
            if in_deg[parent] == 0:
                q.append(parent)

    topo_rank: dict[int, int] = {m: i for i, m in enumerate(order)}
    trans_bits: dict[int, int] = {m: 0 for m in mid_list}

    if len(order) == len(mid_list):
        for m in order:
            bits = 0
            for nb in kept_imp[m]:
                bits |= mid_to_bit[nb] | trans_bits[nb]
            trans_bits[m] = bits
    else:
        # Rare fallback if an import cycle exists: assign remaining ranks and compute BFS bits
        next_rank = len(order)
        for m in mid_list:
            if m not in topo_rank:
                topo_rank[m] = next_rank
                next_rank += 1
        for m in mid_list:
            seen: set[int] = set()
            bfs: deque[int] = deque(kept_imp[m])
            bits = 0
            while bfs:
                cur = bfs.popleft()
                if cur in seen or cur == m:
                    continue
                seen.add(cur)
                bits |= mid_to_bit[cur]
                for nxt in kept_imp[cur]:
                    if nxt not in seen:
                        bfs.append(nxt)
            trans_bits[m] = bits

    return topo_rank, mid_to_bit, trans_bits


def plan_consolidation(
    db: sqlite3.Connection | str | Path,
    plan: PrunePlan,
    *,
    min_saved_loc: int = 2,
    top_k: int = 25,
) -> ConsolidationPlan:
    """Compute conservative in-scope exact-duplicate consolidations and hoisted potential.

    Guarantees zero new imports for every planned ``ConsolidationOp``: each duplicate
    ``D`` only delegates to a canonical representative ``C`` already defined earlier in
    the same module or already in ``D``'s kept transitive import closure.
    """
    conn, should_close = _open_db(db)
    try:
        cur = conn.cursor()

        kept_decls: dict[int, dict[str, Any]] = {}
        by_hash: dict[str, list[int]] = defaultdict(list)

        for row in cur.execute(
            "SELECT id, name, short_name, module_id, kind, type_sig, "
            "canonical_type_hash, body_loc, start_line, end_line "
            "FROM declarations "
            "WHERE is_mathlib = 0 AND kind IN ('theorem', 'lemma') "
            "AND canonical_type_hash IS NOT NULL AND canonical_type_hash != ''"
        ):
            did = int(row[0])
            mid = int(row[3] or 0)
            if did not in plan.kept_decl_ids or mid not in plan.kept_modules:
                continue
            type_sig = row[5] or ""
            body_loc = int(row[7] or 0)
            info = {
                "id": did,
                "name": row[1] or "",
                "short_name": row[2] or "",
                "module_id": mid,
                "kind": (row[4] or "").lower(),
                "type_sig": type_sig,
                "hash": row[6] or "",
                "body_loc": body_loc,
                "start_line": int(row[8] or 0),
                "end_line": int(row[9] or 0),
            }
            kept_decls[did] = info
            by_hash[info["hash"]].append(did)

        dup_hash_groups = {h: ids for h, ids in by_hash.items() if len(ids) >= 2}
        dup_candidate_ids = {d for ids in dup_hash_groups.values() for d in ids}

        # Load exact resolved type-level dependency edges for all duplicate candidates
        type_refs: dict[int, set[int]] = defaultdict(set)
        if dup_candidate_ids:
            for src_id, dst_id in cur.execute(
                "SELECT src_id, dst_id FROM edges WHERE kind = 'type'"
            ):
                if src_id in dup_candidate_ids:
                    type_refs[src_id].add(dst_id)

        # Parse structured binder + return signatures
        parsed_headers: dict[int, ParsedHeader] = {}
        for did in dup_candidate_ids:
            ph = parse_signature_structure(kept_decls[did]["type_sig"])
            if ph is not None:
                parsed_headers[did] = ph

        topo_rank, mid_to_bit, trans_bits = _compute_kept_import_dag(
            plan.kept_modules,
            plan.mod_imports,
            collapsed_barrels=plan.collapsed_barrel_modules,
        )

        # Group by (canonical_type_hash, exact type_refs, exact structural_sig_key)
        verified_groups: dict[tuple[str, frozenset[int], Any], list[int]] = defaultdict(list)
        for h, ids in dup_hash_groups.items():
            for did in ids:
                ph = parsed_headers.get(did)
                if ph is None:
                    continue
                key = (h, frozenset(type_refs.get(did, ())), ph.structural_key)
                verified_groups[key].append(did)

        exact_verified_groups = [g for g in verified_groups.values() if len(g) >= 2]

        ops_by_mod: dict[int, list[ConsolidationOp]] = defaultdict(list)
        canon_mods_needed: set[int] = set()
        dup_mods_needed: set[int] = set()
        all_ops: list[ConsolidationOp] = []

        hoistable_groups = 0
        hoistable_redundant = 0
        hoistable_saved_loc = 0
        hoist_summaries: list[dict[str, Any]] = []

        for gids in exact_verified_groups:
            # Sort upstream-first so canonical representatives precede dependents
            gids.sort(
                key=lambda d: (
                    topo_rank.get(kept_decls[d]["module_id"], 10**9),
                    kept_decls[d]["start_line"],
                    kept_decls[d]["body_loc"],
                    d,
                )
            )

            # Hoisted shared-module consolidation potential
            # Estimate genuine proof-only lines saved for redundant copies (keeping the
            # longest/canonical proof so 1-line `*Statement` wrappers don't falsely count
            # the sole full proof as redundant).
            sig_line_est = {
                d: max(1, len(kept_decls[d]["type_sig"].splitlines())) for d in gids
            }
            proof_only_savings = [
                max(0, kept_decls[d]["body_loc"] - sig_line_est[d] - 1) for d in gids
            ]
            # Keep the primary full proof as canonical; only count non-trivial extra proofs
            hoist_order = sorted(
                range(len(gids)),
                key=lambda i: (-proof_only_savings[i], kept_decls[gids[i]]["body_loc"]),
            )
            non_trivial_redundants = [i for i in hoist_order[1:] if proof_only_savings[i] >= min_saved_loc]
            g_hoist_saved = sum(proof_only_savings[i] for i in non_trivial_redundants)
            if g_hoist_saved > 0:
                hoistable_groups += 1
                hoistable_redundant += len(non_trivial_redundants)
                hoistable_saved_loc += g_hoist_saved
                canon_d = kept_decls[gids[hoist_order[0]]]
                hoist_summaries.append(
                    {
                        "canonical_name": canon_d["name"],
                        "canonical_module": plan.mod_path.get(canon_d["module_id"], ""),
                        "group_size": len(gids),
                        "redundant_decls": len(non_trivial_redundants),
                        "estimated_saved_loc": g_hoist_saved,
                        "type_sig_preview": " ".join(canon_d["type_sig"].split())[:140],
                    }
                )

            # Conservative in-scope consolidation (zero new imports!)
            # Track root canonical chosen for each decl to prevent delegation chains
            delegated_to: dict[int, int] = {}

            for d in gids:
                di = kept_decls[d]
                ph_d = parsed_headers[d]
                if not ph_d.safe_for_delegation:
                    continue
                if di["start_line"] <= 0 or di["end_line"] < di["start_line"]:
                    continue

                est_saved = max(0, di["body_loc"] - sig_line_est[d] - 1)
                if est_saved < min_saved_loc:
                    continue

                dm = di["module_id"]
                dm_trans = trans_bits.get(dm, 0)

                chosen_c: int | None = None
                chosen_same_mod = False
                for c in gids:
                    if c == d:
                        continue
                    # Resolve through any already-delegated canonical so we always point to a root
                    root_c = delegated_to.get(c, c)
                    if root_c == d:
                        continue
                    ci = kept_decls[root_c]
                    cm = ci["module_id"]
                    if cm == dm:
                        if ci["start_line"] > 0 and ci["start_line"] < di["start_line"]:
                            chosen_c = root_c
                            chosen_same_mod = True
                            break
                    elif dm_trans & mid_to_bit.get(cm, 0):
                        chosen_c = root_c
                        chosen_same_mod = False
                        break

                if chosen_c is None:
                    continue

                ci = kept_decls[chosen_c]
                if (
                    not ci["name"]
                    or ci["short_name"].startswith(("anon_", "inst_"))
                    or " " in ci["name"]
                ):
                    continue
                delegated_to[d] = chosen_c
                canon_ref = f"_root_.{ci['name']}"
                rhs = build_delegation_rhs(canon_ref, ph_d)

                op = ConsolidationOp(
                    dup_decl_id=d,
                    dup_name=di["name"],
                    dup_short_name=di["short_name"],
                    dup_module_id=dm,
                    dup_module_path=plan.mod_path.get(dm, ""),
                    dup_start_line=di["start_line"],
                    dup_end_line=di["end_line"],
                    dup_body_loc=di["body_loc"],
                    canon_decl_id=chosen_c,
                    canon_name=ci["name"],
                    canon_short_name=ci["short_name"],
                    canon_module_id=ci["module_id"],
                    canon_module_path=plan.mod_path.get(ci["module_id"], ""),
                    canon_start_line=ci["start_line"],
                    canon_end_line=ci["end_line"],
                    same_module=chosen_same_mod,
                    delegation_rhs=rhs,
                    estimated_saved_loc=est_saved,
                    verified=False,
                )
                ops_by_mod[dm].append(op)
                canon_mods_needed.add(ci["module_id"])
                dup_mods_needed.add(dm)
                all_ops.append(op)

        all_ops.sort(key=lambda o: (-o.estimated_saved_loc, o.dup_name))
        hoist_summaries.sort(key=lambda g: (-g["estimated_saved_loc"], -g["group_size"]))

        report = ConsolidationReport(
            analyzed_kept_theorems=len(kept_decls),
            exact_hash_groups=len(dup_hash_groups),
            exact_verified_groups=len(exact_verified_groups),
            in_scope_candidates=len(all_ops),
            in_scope_same_module=sum(1 for o in all_ops if o.same_module),
            in_scope_imported=sum(1 for o in all_ops if not o.same_module),
            in_scope_estimated_saved_loc=sum(o.estimated_saved_loc for o in all_ops),
            hoistable_groups=hoistable_groups,
            hoistable_redundant_decls=hoistable_redundant,
            hoistable_estimated_saved_loc=hoistable_saved_loc,
            top_in_scope_ops=[o.to_dict() for o in all_ops[:top_k]],
            top_hoistable_groups=hoist_summaries[:top_k],
        )

        return ConsolidationPlan(
            ops_by_mod=dict(ops_by_mod),
            canon_mods_needed=canon_mods_needed,
            dup_mods_needed=dup_mods_needed,
            report=report,
        )
    finally:
        if should_close:
            conn.close()


# ---------------------------------------------------------------------------
# Phase 2: Strict Lean 4 source-level context verification
# ---------------------------------------------------------------------------


@dataclass
class _SourceDeclContext:
    """Verified source-level context of a declaration extracted directly from its `.lean` file."""

    is_private: bool
    is_unsafe_modifier: bool
    in_mutual: bool
    has_explicit_section_var: bool
    active_implicit_vars: tuple[tuple[str, str], ...]  # (bracket, canon_type) for referenced vars
    active_universes: frozenset[str]
    namespace_tuple: tuple[str, ...]
    universe_params: str  # e.g. ".{u, v}" or ""
    parsed_header: ParsedHeader | None
    assign_rel_line: int  # 0-based offset from start_line where top-level `:=` lives
    assign_col: int  # char index of `:` in `:=` on that line (in raw source)
    proof_body_nonblank_lines: int
    body_has_structural_line: bool


def _extract_decl_source_context(
    source_text: str,
    start_line: int,
    end_line: int,
) -> _SourceDeclContext | None:
    """Inspect a declaration and its enclosing section/namespace/variable context in source."""
    if start_line <= 0 or end_line < start_line:
        return None

    cleaned_src, _ = strip_comments_and_extract_docstrings(source_text)
    clean_lines = cleaned_src.splitlines()
    raw_lines = source_text.splitlines()
    n_lines = len(clean_lines)
    if start_line > n_lines:
        return None
    end_line = min(end_line, n_lines)

    # Walk top-level scope up to start_line - 1
    scope_stack: list[tuple[str, list[str], int, int]] = []
    ns_segs: list[str] = []
    var_stack: list[BinderEntry] = []
    univ_stack: list[str] = []
    in_mutual = False
    has_unparseable_var = False

    def _pop_scope(end_name: str | None) -> None:
        if not scope_stack:
            return
        if not end_name:
            skind, segs, vdepth, udepth = scope_stack.pop()
            if skind == "namespace" and segs:
                del ns_segs[-len(segs) :]
            del var_stack[vdepth:]
            del univ_stack[udepth:]
            return
        rem = end_name.split(".")
        while rem and scope_stack:
            skind, segs, vdepth, udepth = scope_stack[-1]
            if skind == "section":
                scope_stack.pop()
                del var_stack[vdepth:]
                del univ_stack[udepth:]
                if segs == rem:
                    rem.clear()
                elif segs and len(rem) >= len(segs) and rem[-len(segs) :] == segs:
                    del rem[-len(segs) :]
                continue
            if not segs:
                scope_stack.pop()
                del var_stack[vdepth:]
                del univ_stack[udepth:]
                continue
            if segs == rem:
                scope_stack.pop()
                del ns_segs[-len(segs) :]
                del var_stack[vdepth:]
                del univ_stack[udepth:]
                rem.clear()
            elif len(segs) > len(rem) and segs[-len(rem) :] == rem:
                k = len(rem)
                scope_stack[-1] = (skind, segs[:-k], vdepth, udepth)
                del ns_segs[-k:]
                rem.clear()
            elif len(rem) > len(segs) and rem[-len(segs) :] == segs:
                scope_stack.pop()
                del ns_segs[-len(segs) :]
                del var_stack[vdepth:]
                del univ_stack[udepth:]
                del rem[-len(segs) :]
            else:
                scope_stack.pop()
                del ns_segs[-len(segs) :]
                del var_stack[vdepth:]
                del univ_stack[udepth:]
                break

    for idx in range(start_line - 1):
        ln = clean_lines[idx]
        if not ln or ln[0] in (" ", "\t"):
            continue
        st = ln.strip()
        if not st:
            continue
        if _MUTUAL_LINE_RE.match(st):
            in_mutual = True
            continue
        em = _END_LINE_RE.match(st)
        if em:
            if in_mutual and not em.group(1):
                in_mutual = False
            else:
                _pop_scope(em.group(1))
            continue
        nsm = _NAMESPACE_LINE_RE.match(st)
        if nsm:
            segs = nsm.group(1).split(".")
            scope_stack.append(("namespace", segs, len(var_stack), len(univ_stack)))
            ns_segs.extend(segs)
            continue
        secm = _SECTION_LINE_RE.match(st)
        if secm:
            segs = secm.group(1).split(".") if secm.group(1) else []
            scope_stack.append(("section", segs, len(var_stack), len(univ_stack)))
            continue
        um = _UNIVERSE_DECL_RE.match(st)
        if um:
            univ_stack.extend(um.group(1).split())
            continue
        vm = _VARIABLE_DECL_RE.match(st)
        if vm:
            parsed_v = parse_binder_list(vm.group(1))
            if parsed_v is None:
                # Sentinel stays scoped to the active section/namespace and pops on `end`
                var_stack.append(BinderEntry(bracket="(", var_name="__unparseable__", type_expr="__unparseable__"))
            else:
                var_stack.extend(parsed_v)
            continue

    # Also check modifiers on immediately preceding standalone lines (e.g. `private\ntheorem ...`)
    s0 = start_line - 1
    e0 = end_line - 1
    preceding_mods = ""
    probe = s0 - 1
    while probe >= 0:
        pst = clean_lines[probe].strip()
        if not pst:
            probe -= 1
            continue
        if pst.startswith("@[") or re.fullmatch(
            r"(?:(?:private|protected|public|noncomputable|partial|unsafe|meta|scoped|local)\s*)+",
            pst,
        ):
            preceding_mods = pst + " " + preceding_mods
            probe -= 1
            continue
        break

    block_clean = "\n".join(clean_lines[s0 : e0 + 1])
    dm = _DECL_MOD_HEADER_RE.match(block_clean.lstrip())
    if not dm:
        return None

    prefix_text = preceding_mods + " " + block_clean[: dm.start(1)]
    is_private = bool(re.search(r"\bprivate\b", prefix_text))
    is_unsafe_mod = bool(re.search(r"\b(?:partial|unsafe|scoped|local|meta)\b", prefix_text))

    after_kw = dm.group(2).lstrip()
    nm = _DECL_NAME_RE.match(after_kw)
    if not nm:
        return None
    rest_after_name = after_kw[nm.end() :]

    univ_params = ""
    if rest_after_name.startswith(".{"):
        close_u = rest_after_name.find("}")
        if close_u == -1:
            return None
        univ_params = rest_after_name[: close_u + 1]
        rest_after_name = rest_after_name[close_u + 1 :]

    # Locate top-level `:=` inside the clean declaration block (after name)
    assign_offset_in_rest = find_top_level_assign(rest_after_name)
    if assign_offset_in_rest == -1:
        return None

    header_clean = rest_after_name[:assign_offset_in_rest].strip()
    parsed_hdr = parse_signature_structure(header_clean)

    # Map assign position back to exact (rel_line, col) in clean_lines[s0 : e0 + 1]
    lead_ws = len(block_clean) - len(block_clean.lstrip())
    kw_end_in_block = lead_ws + dm.end(1)
    # Find rest_after_name offset inside block_clean
    after_kw_idx = block_clean.find(after_kw, kw_end_in_block)
    if after_kw_idx == -1:
        return None
    rest_start_in_block = after_kw_idx + nm.end() + len(univ_params)
    assign_abs = rest_start_in_block + assign_offset_in_rest

    prefix_up_to_assign = block_clean[:assign_abs]
    assign_rel_line = prefix_up_to_assign.count("\n")
    last_nl = prefix_up_to_assign.rfind("\n")
    assign_col = assign_abs if last_nl == -1 else assign_abs - last_nl - 1

    # Verify the exact same `:=` sits at (s0 + assign_rel_line, assign_col) in raw_lines
    raw_assign_line = raw_lines[s0 + assign_rel_line]
    if raw_assign_line[assign_col : assign_col + 2] != ":=":
        return None

    # Count non-blank lines in proof body after `:=` and check for structural lines
    proof_lines_nonblank = 0
    body_has_structural = False
    after_assign_same_line = clean_lines[s0 + assign_rel_line][assign_col + 2 :].strip()
    if after_assign_same_line:
        proof_lines_nonblank += 1
    for r_idx in range(s0 + assign_rel_line + 1, e0 + 1):
        cl = clean_lines[r_idx]
        if cl.strip():
            proof_lines_nonblank += 1
        if cl and cl[0] not in (" ", "\t") and _STRUCTURAL_BODY_LINE_RE.match(cl.strip()):
            body_has_structural = True

    # Check active section variables referenced in header_clean
    has_explicit_var = any(
        v.bracket == "(" or bool(_TYPE_STAR_RE.search(v.type_expr)) for v in var_stack
    )
    sig_words = set(_WORD_RE.findall(header_clean))
    # Collect any implicit/instance section vars whose name or type touches sig_words
    # (transitive fixed-point because `[CommRing R]` depends on `{R : Type}`)
    referenced_vars: list[BinderEntry] = []
    if not has_explicit_var and var_stack:
        needed_names = set(sig_words)
        changed = True
        picked_idx: set[int] = set()
        while changed:
            changed = False
            for vi, vb in enumerate(var_stack):
                if vi in picked_idx:
                    continue
                if vb.var_name is not None and vb.var_name in needed_names:
                    picked_idx.add(vi)
                    needed_names.update(_WORD_RE.findall(vb.type_expr))
                    changed = True
                elif vb.bracket == "[":
                    ty_words = set(_WORD_RE.findall(vb.type_expr))
                    if ty_words & needed_names:
                        picked_idx.add(vi)
                        needed_names.update(ty_words)
                        changed = True
        referenced_vars = [var_stack[vi] for vi in sorted(picked_idx)]

    active_imp_key = tuple(
        (vb.bracket, canonicalize_type(vb.type_expr)) for vb in referenced_vars
    )

    return _SourceDeclContext(
        is_private=is_private,
        is_unsafe_modifier=is_unsafe_mod,
        in_mutual=in_mutual,
        has_explicit_section_var=has_explicit_var,
        active_implicit_vars=active_imp_key,
        active_universes=frozenset(univ_stack),
        namespace_tuple=tuple(ns_segs),
        universe_params=univ_params,
        parsed_header=parsed_hdr,
        assign_rel_line=assign_rel_line,
        assign_col=assign_col,
        proof_body_nonblank_lines=proof_lines_nonblank,
        body_has_structural_line=body_has_structural,
    )


def verify_consolidation_plan_with_sources(
    cplan: ConsolidationPlan,
    module_sources: dict[int, str],
    *,
    min_saved_lines: int = 2,
) -> ConsolidationPlan:
    """Strictly verify every planned ``ConsolidationOp`` against real Lean 4 source files.

    Mutates and returns ``cplan`` with only 100%-verified operations retained in
    ``cplan.ops_by_mod`` and updated verification metrics in ``cplan.report``.
    """
    canon_ctx_cache: dict[tuple[int, int, int], _SourceDeclContext | None] = {}

    def _get_ctx(mid: int, s_line: int, e_line: int) -> _SourceDeclContext | None:
        key = (mid, s_line, e_line)
        if key not in canon_ctx_cache:
            src = module_sources.get(mid)
            if src is None:
                canon_ctx_cache[key] = None
            else:
                canon_ctx_cache[key] = _extract_decl_source_context(src, s_line, e_line)
        return canon_ctx_cache[key]

    verified_by_mod: dict[int, list[ConsolidationOp]] = defaultdict(list)
    verified_cnt = 0
    skipped_cnt = 0

    for dm, ops in cplan.ops_by_mod.items():
        for op in ops:
            c_ctx = _get_ctx(op.canon_module_id, op.canon_start_line, op.canon_end_line)
            d_ctx = _get_ctx(op.dup_module_id, op.dup_start_line, op.dup_end_line)
            if c_ctx is None or d_ctx is None:
                skipped_cnt += 1
                continue

            # Never delegate to/from unsafe, mutual, or explicit-section-variable decls
            if (
                c_ctx.is_unsafe_modifier
                or d_ctx.is_unsafe_modifier
                or c_ctx.in_mutual
                or d_ctx.in_mutual
                or c_ctx.has_explicit_section_var
                or d_ctx.has_explicit_section_var
                or d_ctx.body_has_structural_line
            ):
                skipped_cnt += 1
                continue

            # Private canonical target can only be referenced inside the same module & namespace
            if c_ctx.is_private:
                if not op.same_module or c_ctx.namespace_tuple != d_ctx.namespace_tuple:
                    skipped_cnt += 1
                    continue

            # Both must parse cleanly from actual source (eliminates letI truncation!)
            if c_ctx.parsed_header is None or d_ctx.parsed_header is None:
                skipped_cnt += 1
                continue
            if not d_ctx.parsed_header.safe_for_delegation:
                skipped_cnt += 1
                continue

            # Exact structural match on full source headers
            if c_ctx.parsed_header.structural_key != d_ctx.parsed_header.structural_key:
                skipped_cnt += 1
                continue

            # Exact universe param & active implicit/instance section variable match
            if c_ctx.universe_params != d_ctx.universe_params:
                skipped_cnt += 1
                continue
            if c_ctx.active_implicit_vars != d_ctx.active_implicit_vars:
                skipped_cnt += 1
                continue
            # If universe vars from `universe u` appear in header, require matching universe scope
            if c_ctx.active_universes or d_ctx.active_universes:
                hdr_words = set(_WORD_RE.findall(d_ctx.parsed_header.ret_type)) | {
                    w
                    for b in d_ctx.parsed_header.binders
                    for w in _WORD_RE.findall(b.type_expr)
                }
                used_c_u = c_ctx.active_universes & hdr_words
                used_d_u = d_ctx.active_universes & hdr_words
                if used_c_u != used_d_u:
                    skipped_cnt += 1
                    continue

            # Ensure replacing the proof body genuinely saves lines
            actual_saved = d_ctx.proof_body_nonblank_lines - 1
            if actual_saved < min_saved_lines:
                skipped_cnt += 1
                continue

            # Build final safe reference (short name for same-module private, _root_. otherwise)
            canon_ref = (
                op.canon_short_name
                if (c_ctx.is_private and op.same_module)
                else f"_root_.{op.canon_name}"
            )
            op.delegation_rhs = build_delegation_rhs(canon_ref, d_ctx.parsed_header)
            op.estimated_saved_loc = actual_saved
            op.verified = True

            verified_by_mod[dm].append(op)
            verified_cnt += 1

    cplan.ops_by_mod = dict(verified_by_mod)
    cplan.report.source_verified_ops = verified_cnt
    cplan.report.source_skipped_ops = skipped_cnt
    return cplan


def apply_consolidations_to_lines(
    lines: list[str],
    ops: Iterable[ConsolidationOp],
    *,
    strip_line_mask: bytearray | None = None,
) -> tuple[list[str], int, int]:
    """Apply verified 1-line proof delegations to ``lines`` (in-place safe, reverse line order).

    Returns ``(new_lines, applied_count, saved_nonblank_lines)``.
    Also updates ``strip_line_mask`` (if provided) when lines are removed so downstream
    passes see consistent indices.
    """
    sorted_ops = sorted(ops, key=lambda o: o.dup_start_line, reverse=True)
    if not sorted_ops:
        return lines, 0, 0

    raw_text = "\n".join(lines)
    applied = 0
    saved_lines = 0

    for op in sorted_ops:
        s0 = op.dup_start_line - 1
        e0 = min(len(lines) - 1, op.dup_end_line - 1)
        if s0 < 0 or e0 < s0 or s0 >= len(lines):
            continue
        if strip_line_mask is not None and any(
            strip_line_mask[i] for i in range(s0, min(e0 + 1, len(strip_line_mask)))
        ):
            continue

        ctx = _extract_decl_source_context(raw_text, op.dup_start_line, op.dup_end_line)
        if ctx is None or ctx.body_has_structural_line:
            continue

        assign_idx = s0 + ctx.assign_rel_line
        if assign_idx > e0 or assign_idx >= len(lines):
            continue

        assign_line = lines[assign_idx]
        if assign_line[ctx.assign_col : ctx.assign_col + 2] != ":=":
            continue

        # Count non-blank lines removed from proof body
        before_nonblank = 0
        if assign_line[ctx.assign_col + 2 :].strip():
            before_nonblank += 1
        for idx in range(assign_idx + 1, e0 + 1):
            if lines[idx].strip():
                before_nonblank += 1

        if before_nonblank <= 1:
            continue

        # Replace everything from `:=` through `e0` with `:= <delegation_rhs>`
        new_assign_line = assign_line[: ctx.assign_col + 2] + " " + op.delegation_rhs
        lines[assign_idx] = new_assign_line
        del lines[assign_idx + 1 : e0 + 1]
        if strip_line_mask is not None:
            del strip_line_mask[assign_idx + 1 : e0 + 1]

        applied += 1
        saved_lines += before_nonblank - 1

    return lines, applied, saved_lines
