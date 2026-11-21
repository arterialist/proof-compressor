"""Stage 4 refactoring target selector and formal work-order emitter."""

from __future__ import annotations

import json
import re
import sqlite3
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from proof_compressor.expose._db import (
    DbHandle,
    get_cluster_hierarchy,
    has_reachable_metrics,
    open_db,
    query_all,
    safe_json_loads,
)


@dataclass
class RefactorWorkOrder:
    """Self-contained refactoring work order anchored to a formal interface contract."""

    order_id: str
    scope: str  # "cluster" or "module"
    title: str
    priority_score: float
    internal_loc: int
    decl_count: int
    interface_width: int
    leverage_ratio: float
    estimated_loc_savings: int
    bookkeeping_ratio: float
    rationale_tags: list[str] = field(default_factory=list)
    target_modules: list[str] = field(default_factory=list)
    interface_in: list[dict[str, Any]] = field(default_factory=list)
    interface_out: list[dict[str, Any]] = field(default_factory=list)
    duplicate_groups: list[dict[str, Any]] = field(default_factory=list)
    hypothesis_slack_candidates: list[dict[str, Any]] = field(default_factory=list)
    strategy: str = ""
    verification_checklist: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _count_explicit_hypotheses(type_sig: str) -> int:
    """Estimate number of explicit hypotheses/arrows in a Lean type signature."""
    if not type_sig:
        return 0
    s = " ".join(type_sig.split())
    # Count top-level arrows and explicit `(h : ...)` binders
    arrows = s.count("→") + s.count("->")
    binders = len(re.findall(r"\([^():]+:[^()]+\)", s))
    return max(arrows, binders)


def _compute_target_metrics(
    decls: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], float, int]:
    """Extract duplicate groups, hypothesis-slack candidates, bookkeeping ratio, and dup LOC."""
    if not decls:
        return [], [], 0.0, 0

    by_hash: dict[str, list[dict[str, Any]]] = defaultdict(list)
    bk_count = 0
    slack_candidates: list[dict[str, Any]] = []

    for d in decls:
        if int(d.get("is_bookkeeping") or 0):
            bk_count += 1
        h = str(d.get("canonical_type_hash") or "").strip()
        if h:
            by_hash[h].append(d)
        if d.get("kind") in ("theorem", "lemma"):
            hcount = _count_explicit_hypotheses(str(d.get("type_sig") or ""))
            body_loc = int(d.get("body_loc") or 0)
            if hcount >= 5 and body_loc >= 15:
                slack_candidates.append(
                    {
                        "name": str(d["name"]),
                        "hypothesis_count": hcount,
                        "body_loc": body_loc,
                    }
                )

    dup_groups: list[dict[str, Any]] = []
    redundant_loc = 0
    for h, items in by_hash.items():
        if len(items) > 1:
            locs = [int(it.get("body_loc") or 0) for it in items]
            min_loc = min(locs) if locs else 0
            saved = max(0, sum(locs) - min_loc)
            redundant_loc += saved
            dup_groups.append(
                {
                    "canonical_type_hash": h,
                    "count": len(items),
                    "redundant_loc": saved,
                    "names": [str(it["name"]) for it in items[:8]],
                }
            )

    dup_groups.sort(key=lambda g: (-g["redundant_loc"], -g["count"]))
    slack_candidates.sort(key=lambda c: (-c["hypothesis_count"], -c["body_loc"]))
    bk_ratio = bk_count / len(decls)
    return dup_groups[:10], slack_candidates[:8], round(bk_ratio, 3), redundant_loc


def _build_strategy(
    rationale_tags: list[str],
    dup_groups: list[dict[str, Any]],
    slack_candidates: list[dict[str, Any]],
    bk_ratio: float,
    interface_width: int,
) -> str:
    """Synthesize a concise, actionable refactoring strategy."""
    steps: list[str] = []
    if dup_groups:
        steps.append(
            f"Deduplicate {len(dup_groups)} canonical signature group(s) into shared reusable lemmas."
        )
    if bk_ratio >= 0.35:
        steps.append(
            f"Collapse routine formalization glue ({bk_ratio * 100:.0f}% bookkeeping declarations) "
            "using higher-level automation (`aesop`/`positivity`/`fun_prop`) or Mathlib APIs."
        )
    if slack_candidates:
        steps.append(
            f"Audit {len(slack_candidates)} high-hypothesis lemma(s) for unused/redundant hypotheses "
            "and factor shared context into a tighter abstraction."
        )
    if interface_width <= 8:
        steps.append(
            f"Exploit the narrow boundary ({interface_width} interface items) to replace internal "
            "proof machinery wholesale while preserving exact exported signatures."
        )
    if not steps:
        steps.append(
            "Inline single-use intermediate helpers and replace verbose tactic blocks with concise "
            "structural proofs preserving all exported outputs."
        )
    return " ".join(steps)


def _format_interface_entries(items: list[dict[str, Any]], limit: int = 12) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for it in items[:limit]:
        if not isinstance(it, dict) or not it.get("name"):
            continue
        out.append(
            {
                "name": str(it["name"]),
                "kind": str(it.get("kind") or ""),
                "type_sig": str(it.get("type_sig") or "")[:300],
            }
        )
    return out


def _plan_from_clusters(
    conn: sqlite3.Connection,
    *,
    min_loc: int,
) -> list[RefactorWorkOrder]:
    """Score cluster-level refactoring targets (preferring leaf sections, fallback to chapters)."""
    chapters, sections_by_chapter, _c2c = get_cluster_hierarchy(conn)
    if not chapters:
        return []

    # Prefer section-level clusters (level=1) when present, since they are tighter work units
    candidates: list[dict[str, Any]] = []
    for chap in chapters:
        secs = sections_by_chapter.get(int(chap["id"]), [])
        if secs:
            candidates.extend(secs)
        else:
            candidates.append(chap)

    orders: list[RefactorWorkOrder] = []
    for cl in candidates:
        cid = int(cl["id"])
        total_loc = int(cl.get("total_loc") or 0)
        if total_loc < min_loc:
            continue

        decls = query_all(
            conn,
            """
            SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.canonical_type_hash,
                   d.body_loc, d.is_bookkeeping, COALESCE(mod.path, '') AS module_path
            FROM declarations d
            JOIN metrics m ON m.decl_id = d.id
            LEFT JOIN modules mod ON mod.id = d.module_id
            WHERE m.cluster_id = ?
              AND m.reachable = 1
              AND d.is_mathlib = 0
            """,
            (cid,),
        )
        if not decls:
            continue

        internal_loc = max(total_loc, sum(int(d["body_loc"] or 0) for d in decls))
        if internal_loc < min_loc:
            continue

        in_items = safe_json_loads(cl.get("interface_in_json"), [])
        out_items = safe_json_loads(cl.get("interface_out_json"), [])
        proj_in = [it for it in in_items if isinstance(it, dict) and not it.get("is_mathlib")]
        proj_out = [it for it in out_items if isinstance(it, dict) and not it.get("is_mathlib")]
        if not proj_out:
            # Fallback: highest-LOC theorems/defs in this cluster
            proj_out = [
                {
                    "name": d["name"],
                    "kind": d["kind"],
                    "type_sig": d["type_sig"],
                }
                for d in sorted(decls, key=lambda x: -int(x["body_loc"] or 0))[:5]
            ]

        interface_width = max(1, len(proj_in) + len(proj_out))
        leverage_ratio = round(internal_loc / interface_width, 2)
        dup_groups, slack_cands, bk_ratio, dup_loc = _compute_target_metrics(decls)

        est_savings = int(
            dup_loc
            + internal_loc * min(0.35, bk_ratio * 0.45)
            + len(slack_cands) * 12
        )
        est_savings = min(int(internal_loc * 0.75), max(est_savings, int(internal_loc * 0.15)))

        rationale_tags: list[str] = []
        if internal_loc >= 300:
            rationale_tags.append("high_internal_loc")
        if leverage_ratio >= 25.0 or interface_width <= 8:
            rationale_tags.append("narrow_interface")
        if dup_groups:
            rationale_tags.append("duplicate_lemmas")
        if slack_cands:
            rationale_tags.append("hypothesis_slack")
        if bk_ratio >= 0.35:
            rationale_tags.append("high_bookkeeping_ratio")

        priority = round(
            (internal_loc * 0.35)
            + (leverage_ratio * 2.0)
            + (dup_loc * 1.5)
            + (bk_ratio * 80.0)
            + (len(slack_cands) * 15.0),
            2,
        )

        modules = sorted({str(d["module_path"]) for d in decls if d["module_path"]})
        title = str(cl.get("title") or f"Cluster {cid}")
        strategy = _build_strategy(
            rationale_tags, dup_groups, slack_cands, bk_ratio, interface_width
        )

        orders.append(
            RefactorWorkOrder(
                order_id=f"cluster-{cid}",
                scope="cluster",
                title=title,
                priority_score=priority,
                internal_loc=internal_loc,
                decl_count=len(decls),
                interface_width=interface_width,
                leverage_ratio=leverage_ratio,
                estimated_loc_savings=est_savings,
                bookkeeping_ratio=bk_ratio,
                rationale_tags=rationale_tags,
                target_modules=modules[:20],
                interface_in=_format_interface_entries(proj_in),
                interface_out=_format_interface_entries(proj_out),
                duplicate_groups=dup_groups,
                hypothesis_slack_candidates=slack_cands,
                strategy=strategy,
                verification_checklist=[
                    f"Run `lake build {' '.join(modules[:3])}` with exit code 0" if modules else "Run `lake build` with exit code 0",
                    "Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs",
                    f"Verify strict effective LOC reduction (< {internal_loc} LOC)",
                ],
            )
        )

    return orders


def _plan_from_modules(
    conn: sqlite3.Connection,
    *,
    min_loc: int,
    limit_modules: int = 80,
) -> list[RefactorWorkOrder]:
    """Fallback module-level refactoring target planner when clusters are absent."""
    use_reach = has_reachable_metrics(conn)
    if use_reach:
        mod_rows = query_all(
            conn,
            """
            SELECT mod.id, mod.path, mod.loc,
                   COUNT(d.id) AS decl_count,
                   COALESCE(SUM(d.body_loc), 0) AS body_loc
            FROM modules mod
            JOIN declarations d ON d.module_id = mod.id
            JOIN metrics m ON m.decl_id = d.id
            WHERE m.reachable = 1 AND mod.is_mathlib = 0 AND d.is_mathlib = 0
            GROUP BY mod.id
            HAVING MAX(mod.loc, COALESCE(SUM(d.body_loc), 0)) >= ?
            ORDER BY body_loc DESC
            LIMIT ?
            """,
            (min_loc, limit_modules),
        )
    else:
        mod_rows = query_all(
            conn,
            """
            SELECT mod.id, mod.path, mod.loc,
                   COUNT(d.id) AS decl_count,
                   COALESCE(SUM(d.body_loc), 0) AS body_loc
            FROM modules mod
            JOIN declarations d ON d.module_id = mod.id
            WHERE mod.is_mathlib = 0 AND d.is_mathlib = 0
            GROUP BY mod.id
            HAVING MAX(mod.loc, COALESCE(SUM(d.body_loc), 0)) >= ?
            ORDER BY body_loc DESC
            LIMIT ?
            """,
            (min_loc, limit_modules),
        )

    orders: list[RefactorWorkOrder] = []
    for mr in mod_rows:
        mid = int(mr["id"])
        mpath = str(mr["path"])
        decls = query_all(
            conn,
            """
            SELECT id, name, short_name, kind, type_sig, canonical_type_hash,
                   body_loc, is_bookkeeping
            FROM declarations
            WHERE module_id = ? AND is_mathlib = 0
            """,
            (mid,),
        )
        if not decls:
            continue

        internal_loc = max(int(mr["loc"] or 0), int(mr["body_loc"] or 0))
        decl_ids = [int(d["id"]) for d in decls]
        ph = ",".join("?" for _ in decl_ids)

        # Cross-module inputs & outputs
        in_rows = query_all(
            conn,
            f"""
            SELECT DISTINCT d.name, d.kind, d.type_sig
            FROM edges e
            JOIN declarations d ON d.id = e.dst_id
            WHERE e.src_id IN ({ph})
              AND d.module_id != ?
              AND d.is_mathlib = 0
            LIMIT 25
            """,
            (*decl_ids, mid),
        )
        out_rows = query_all(
            conn,
            f"""
            SELECT DISTINCT d.name, d.kind, d.type_sig
            FROM edges e
            JOIN declarations d ON d.id = e.dst_id
            JOIN declarations src ON src.id = e.src_id
            WHERE e.dst_id IN ({ph})
              AND src.module_id != ?
              AND src.is_mathlib = 0
            LIMIT 25
            """,
            (*decl_ids, mid),
        )
        if not out_rows:
            out_rows = [
                {"name": d["name"], "kind": d["kind"], "type_sig": d["type_sig"]}
                for d in sorted(decls, key=lambda x: -int(x["body_loc"] or 0))[:5]
            ]

        interface_width = max(1, len(in_rows) + len(out_rows))
        leverage_ratio = round(internal_loc / interface_width, 2)
        dup_groups, slack_cands, bk_ratio, dup_loc = _compute_target_metrics(decls)

        est_savings = int(
            dup_loc + internal_loc * min(0.35, bk_ratio * 0.45) + len(slack_cands) * 12
        )
        est_savings = min(int(internal_loc * 0.75), max(est_savings, int(internal_loc * 0.15)))

        rationale_tags: list[str] = []
        if internal_loc >= 200:
            rationale_tags.append("high_internal_loc")
        if leverage_ratio >= 20.0 or interface_width <= 6:
            rationale_tags.append("narrow_interface")
        if dup_groups:
            rationale_tags.append("duplicate_lemmas")
        if slack_cands:
            rationale_tags.append("hypothesis_slack")
        if bk_ratio >= 0.35:
            rationale_tags.append("high_bookkeeping_ratio")

        priority = round(
            (internal_loc * 0.35)
            + (leverage_ratio * 2.0)
            + (dup_loc * 1.5)
            + (bk_ratio * 80.0)
            + (len(slack_cands) * 15.0),
            2,
        )
        strategy = _build_strategy(
            rationale_tags, dup_groups, slack_cands, bk_ratio, interface_width
        )

        orders.append(
            RefactorWorkOrder(
                order_id=f"module-{mid}",
                scope="module",
                title=mpath,
                priority_score=priority,
                internal_loc=internal_loc,
                decl_count=len(decls),
                interface_width=interface_width,
                leverage_ratio=leverage_ratio,
                estimated_loc_savings=est_savings,
                bookkeeping_ratio=bk_ratio,
                rationale_tags=rationale_tags,
                target_modules=[mpath],
                interface_in=_format_interface_entries(in_rows),
                interface_out=_format_interface_entries(out_rows),
                duplicate_groups=dup_groups,
                hypothesis_slack_candidates=slack_cands,
                strategy=strategy,
                verification_checklist=[
                    f"Run `lake build {mpath}` with exit code 0",
                    "Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on exported outputs",
                    f"Verify strict effective LOC reduction (< {internal_loc} LOC)",
                ],
            )
        )

    return orders


def plan_refactors(
    db: DbHandle,
    *,
    top_k: int = 20,
    min_loc: int = 30,
    output_path: str | Path | None = None,
) -> list[dict[str, Any]]:
    """Select the highest-leverage Stage 4 refactoring targets and emit work orders."""
    with open_db(db, readonly=False) as conn:
        orders = _plan_from_clusters(conn, min_loc=min_loc)
        if not orders:
            orders = _plan_from_modules(conn, min_loc=min_loc)

    orders.sort(key=lambda o: (-o.priority_score, -o.internal_loc, o.order_id))
    selected = [o.to_dict() for o in orders[:top_k]]

    if output_path is not None:
        out = Path(output_path)
        out.parent.mkdir(parents=True, exist_ok=True)
        if out.suffix.lower() == ".md":
            out.write_text(format_refactor_plan_markdown(selected), encoding="utf-8")
        else:
            out.write_text(json.dumps(selected, indent=2), encoding="utf-8")

    return selected


def format_refactor_plan_markdown(work_orders: list[dict[str, Any]]) -> str:
    """Format refactoring work orders as a readable Markdown plan."""
    lines = [
        "# Kernel-Checked Refactoring Plan",
        "",
        f"Total selected work orders: **{len(work_orders)}**",
        "",
    ]
    if not work_orders:
        lines.append("_No refactoring targets met the minimum LOC threshold._")
        return "\n".join(lines) + "\n"

    lines.extend(
        [
            "| # | Target | Scope | Internal LOC | Interface Width | Est. Savings | Priority | Rationale |",
            "|---:|---|---|---:|---:|---:|---:|---|",
        ]
    )
    for idx, wo in enumerate(work_orders, start=1):
        tags = ", ".join(wo.get("rationale_tags", [])) or "general"
        lines.append(
            f"| {idx} | `{wo['title']}` | {wo['scope']} | {wo['internal_loc']:,} | "
            f"{wo['interface_width']} | {wo['estimated_loc_savings']:,} | "
            f"{wo['priority_score']:.1f} | {tags} |"
        )
    lines.append("")

    for idx, wo in enumerate(work_orders, start=1):
        lines.append(f"## Work Order {idx}: `{wo['title']}` (`{wo['order_id']}`)")
        lines.append("")
        lines.append(
            f"- **Internal LOC:** {wo['internal_loc']:,} ({wo['decl_count']} declarations; "
            f"bookkeeping ratio {wo['bookkeeping_ratio'] * 100:.1f}%)"
        )
        lines.append(
            f"- **Formal Interface Width:** {wo['interface_width']} "
            f"(leverage ratio {wo['leverage_ratio']} LOC/item)"
        )
        lines.append(f"- **Estimated Savings:** ~{wo['estimated_loc_savings']:,} LOC")
        lines.append(f"- **Strategy:** {wo['strategy']}")
        if wo.get("interface_in"):
            in_names = ", ".join(f"`{i['name']}`" for i in wo["interface_in"][:8])
            lines.append(f"- **Inputs:** {in_names}")
        if wo.get("interface_out"):
            out_names = ", ".join(f"`{o['name']}`" for o in wo["interface_out"][:8])
            lines.append(f"- **Outputs (must preserve exactly):** {out_names}")
        if wo.get("duplicate_groups"):
            lines.append(f"- **Duplicate Signature Groups:** {len(wo['duplicate_groups'])}")
        if wo.get("verification_checklist"):
            lines.append("- **Verification Gate:**")
            for chk in wo["verification_checklist"]:
                lines.append(f"  - [ ] {chk}")
        lines.append("")

    return "\n".join(lines).strip() + "\n"
