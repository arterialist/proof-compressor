"""Automated statement-fidelity and dependency-graph auditor for generated LaTeX."""

from __future__ import annotations

import json
import re
import sqlite3
from collections import deque
from pathlib import Path
from typing import Any

from proof_compressor.expose._db import (
    DbHandle,
    has_reachable_metrics,
    open_db,
    query_all,
)
from proof_compressor.expose.filter import detect_bookkeeping_leaks
from proof_compressor.expose.symbols import (
    SymbolRegistry,
    _GLUE_HYPOTHESIS_RE,
    _strip_balanced_blocks,
    lean_type_to_latex,
)

# Standard LaTeX / AMS / geometry / booktabs / hyperref macros allowed outside the symbol registry
_STANDARD_TEX_MACROS = frozenset(
    {
        # Document & structure
        "documentclass", "usepackage", "title", "author", "date", "maketitle",
        "tableofcontents", "begin", "end", "section", "subsection", "subsubsection",
        "paragraph", "subparagraph", "appendix", "label", "ref", "eqref", "pageref",
        "cite", "footnote", "item", "caption", "centering", "noindent", "par",
        "newline", "linebreak", "pagebreak", "clearpage", "newpage", "hfill",
        "vfill", "hspace", "vspace", "quad", "qquad", "smallskip", "medskip",
        "bigskip", "today", "href", "url", "hyperref", "texorpdfstring",
        # Definitions & macros
        "newcommand", "renewcommand", "providecommand", "DeclareMathOperator",
        "newtheorem", "theoremstyle", "detokenize", "leanlink", "leanmod",
        "allowbreak", "nolinkurl", "expandafter", "emergencystretch", "sloppy",
        "fussy", "flushleft", "center", "leftskip", "rightskip", "raggedright",
        "arraybackslash", "textwidth",
        # Text styling
        "textbf", "textit", "texttt", "textrm", "textsf", "textsc", "textup",
        "emph", "text", "mbox", "hbox", "vbox", "tiny", "scriptsize", "footnotesize",
        "small", "normalsize", "large", "Large", "LARGE", "huge", "Huge",
        "textsuperscript", "textsubscript", "textbackslash", "textasciitilde",
        "textasciicircum", "LaTeX", "TeX",
        # Tables (booktabs)
        "toprule", "midrule", "bottomrule", "hline", "cline", "multicolumn",
        "multirow", "cmidrule",
        # Math fonts & operators
        "mathbb", "mathcal", "mathfrak", "mathrm", "mathbf", "mathsf", "mathit",
        "mathtt", "mathscr", "boldsymbol", "bm", "operatorname", "limits", "nolimits",
        "displaystyle", "textstyle", "scriptstyle", "scriptscriptstyle",
        "overline", "underline", "widehat", "widetilde", "hat", "tilde", "bar",
        "vec", "dot", "ddot", "check", "acute", "grave", "breve", "mathring",
        # Delimiters & fractions
        "left", "right", "big", "Big", "bigg", "Bigg", "bigl", "bigr", "Bigl",
        "Bigr", "biggl", "biggr", "Biggl", "Biggr", "middle", "frac", "dfrac",
        "tfrac", "cfrac", "binom", "dbinom", "tbinom", "sqrt", "nthroot",
        "langle", "rangle", "lfloor", "rfloor", "lceil", "rceil", "lvert", "rvert",
        "lVert", "rVert", "vert", "Vert", "backslash",
        # Big operators & functions
        "sum", "prod", "coprod", "int", "iint", "iiint", "oint", "bigcup",
        "bigcap", "bigoplus", "bigotimes", "bigvee", "bigwedge", "bigsqcup",
        "lim", "limsup", "liminf", "sup", "inf", "max", "min", "arg", "deg",
        "det", "dim", "exp", "gcd", "hom", "ker", "lg", "ln", "log", "Pr",
        "sec", "sin", "sinh", "cos", "cosh", "tan", "tanh", "cot", "coth",
        "csc", "arcsin", "arccos", "arctan", "Re", "Im", "mod", "bmod", "pmod",
        "pod", "substack", "overset", "underset", "stackrel",
        # Relations & arrows & logic
        "forall", "exists", "nexists", "neg", "lnot", "land", "lor", "wedge",
        "vee", "to", "gets", "mapsto", "longmapsto", "rightarrow", "leftarrow",
        "Rightarrow", "Leftarrow", "leftrightarrow", "Leftrightarrow", "iff",
        "implies", "impliedby", "hookrightarrow", "hookleftarrow", "twoheadrightarrow",
        "longrightarrow", "longleftarrow", "xrightarrow", "xleftarrow", "sim",
        "simeq", "approx", "cong", "equiv", "propto", "le", "leq", "leqslant",
        "ge", "geq", "geqslant", "ll", "gg", "ne", "neq", "not", "in", "notin",
        "ni", "subset", "subseteq", "supset", "supseteq", "subsetneq", "supsetneq",
        "prec", "preceq", "succ", "succeq", "vdash", "dashv", "models", "perp",
        "parallel", "mid", "nmid", "divides", "asymp", "bowtie", "smile", "frown",
        # Binary ops & misc symbols
        "pm", "mp", "times", "div", "cdot", "cdots", "ldots", "dots", "vdots",
        "ddots", "circ", "bullet", "star", "ast", "oplus", "ominus", "otimes",
        "oslash", "odot", "cup", "cap", "setminus", "sqcup", "sqcap", "dagger",
        "ddagger", "amalg", "wr", "infty", "partial", "nabla", "emptyset",
        "varnothing", "aleph", "beth", "hbar", "ell", "wp", "angle", "triangle",
        "square", "blacksquare", "qed", "qedhere", "prime", "backprime", "flat",
        "natural", "sharp", "clubsuit", "diamondsuit", "heartsuit", "spadesuit",
        "top", "bot", "colon", "quad", "qquad",
        # Greek letters
        "alpha", "beta", "gamma", "delta", "epsilon", "varepsilon", "zeta",
        "eta", "theta", "vartheta", "iota", "kappa", "varkappa", "lambda", "mu",
        "nu", "xi", "pi", "varpi", "rho", "varrho", "sigma", "varsigma", "tau",
        "upsilon", "phi", "varphi", "chi", "psi", "omega",
        "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Upsilon",
        "Phi", "Psi", "Omega",
        # Spacing / alignment
        "cr", "tag", "notag", "nonumber", "intertext", "shortintertext", "phantom",
        "hphantom", "vphantom", "mathclap", "smash", "rlap", "llap",
    }
)

_LEANLINK_RE = re.compile(r"\\leanlink(?:\[[^\]]*\])?\{([^}]+)\}")

_THEOREM_BLOCK_RE = re.compile(
    r"\\begin\{(theorem|proposition|lemma|corollary)\}(.*?)\\end\{\1\}"
    r"(?:\s*\\begin\{proof\}(.*?)\\end\{proof\})?",
    re.S,
)

_MACRO_DEF_RE = re.compile(
    r"\\(?:newcommand|renewcommand|providecommand|DeclareMathOperator)\*?\{\\([A-Za-z]+)\}"
)

_MACRO_USE_RE = re.compile(r"\\([A-Za-z]+)")


def _line_of_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _extract_lean_hypotheses(type_sig: str) -> list[str]:
    """Extract substantive mathematical hypothesis clauses from a Lean type signature."""
    if not type_sig:
        return []
    s = " ".join(type_sig.split())
    if s.startswith(":"):
        s = s[1:].strip()
    s = _strip_balanced_blocks(s, "[", "]")
    s = _strip_balanced_blocks(s, "{", "}")
    s = _strip_balanced_blocks(s, "⦃", "⦄")

    # Split at top-level arrows `→` / `->`
    parts: list[str] = []
    depth = 0
    buf: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch in "([{":
            depth += 1
            buf.append(ch)
        elif ch in ")]}":
            depth = max(0, depth - 1)
            buf.append(ch)
        elif depth == 0 and ch == "→":
            parts.append("".join(buf).strip())
            buf = []
        elif depth == 0 and s[i : i + 2] == "->":
            parts.append("".join(buf).strip())
            buf = []
            i += 1
        else:
            buf.append(ch)
        i += 1
    if buf:
        parts.append("".join(buf).strip())

    # All parts except the final conclusion are hypotheses; also inspect explicit `(h : P)` binders
    hyps: list[str] = []
    for p in parts[:-1]:
        if not p or _GLUE_HYPOTHESIS_RE.search(p):
            continue
        # Skip bare variable-typing binders like `(s : ℂ)` unless they carry a predicate/relation
        hyps.append(p)

    # Also extract parenthesized hypothesis binders before `:` or `,` inside the first segment
    for m in re.finditer(r"\(([^()]+:[^()]+)\)", s):
        clause = m.group(1).strip()
        if clause.startswith(("fun ", "λ")):
            continue
        if _GLUE_HYPOTHESIS_RE.search(clause):
            continue
        rhs = clause.split(":", 1)[1].strip()
        if "=>" in rhs or "↦" in rhs:
            continue
        # Filter out pure carrier types like `x : ℝ`, `n : ℕ`
        if rhs in {"ℝ", "ℂ", "ℕ", "ℤ", "ℚ", "Real", "Complex", "Nat", "Int", "Rat", "Type", "Prop"}:
            continue
        if any(tok in rhs for tok in ("<", ">", "≤", "≥", "≠", "=", "Prime", "Primitive", "Nonzero", "Pos", "Odd", "Even", "Cusp", "Compact", "Irrational", "Converge", "Bounded", "Hermitian", "Unitary")):
            if rhs not in hyps:
                hyps.append(rhs)

    return hyps


def _strip_theorem_header_for_stmt_check(stmt_body: str) -> str:
    """Strip optional `[Title]`, `\\leanlink{...}`, and `\\label{...}` before checking statement fidelity."""
    s = stmt_body.lstrip()
    if s.startswith("["):
        depth = 0
        end_idx = -1
        for i, ch in enumerate(s):
            if ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
                if depth == 0:
                    end_idx = i
                    break
        if end_idx >= 0:
            s = s[end_idx + 1 :]
    s = _LEANLINK_RE.sub(" ", s)
    s = re.sub(r"\\label\{[^}]*\}", " ", s)
    return s.strip()


def _hypothesis_present_in_latex(
    hyp: str,
    stmt_latex: str,
    registry: SymbolRegistry | None = None,
) -> bool:
    """Check whether key mathematical markers of a Lean hypothesis survive in the LaTeX statement."""
    stmt_lower = stmt_latex.lower()
    hyp_tex = lean_type_to_latex(hyp, registry)
    hyp_tex_lower = hyp_tex.lower()

    # Check relation / comparison operators
    rel_checks: tuple[tuple[tuple[str, ...], tuple[str, ...]], ...] = (
        (("≠", "!="), (r"\neq", r"\ne ", "!=", "≠", "nonzero", "non-zero", "not equal")),
        (("≤", "<="), (r"\le", "<=", "≤")),
        (("≥", ">="), (r"\ge", ">=", "≥")),
        (("<",), ("<", r"\lt", "less than", "positive")),
        ((">",), (">", r"\gt", "greater than", "positive")),
    )
    for lean_ops, tex_ops in rel_checks:
        if any(op in hyp for op in lean_ops):
            if not any(top in stmt_lower for top in tex_ops):
                return False

    # Check salient mathematical predicates (Prime, Primitive, Even, Odd, Pos, etc.)
    salient = re.findall(
        r"\b(Prime|Primitive|IsPrimitive|Even|Odd|Pos|Neg|Nonneg|Cusp|Cuspidal|"
        r"Bounded|Compact|Convergent|Unitary|Hermitian|Irreducible|Simple|Finite|"
        r"Smooth|Holomorphic|Meromorphic|Analytic|Nonvanishing)\b",
        hyp,
        re.IGNORECASE,
    )
    for word in salient:
        w = word.lower().removeprefix("is")
        if w not in stmt_lower:
            return False

    # Check custom macros translated from the hypothesis (e.g., registered symbols)
    custom_macros = [
        m for m in re.findall(r"\\[A-Za-z]+", hyp_tex)
        if m.lstrip("\\") not in _STANDARD_TEX_MACROS
    ]
    for mac in custom_macros:
        if mac.lower() not in stmt_lower:
            # Also accept the symbol's rendered display name or short name
            entry = registry.by_macro.get(mac) if registry else None
            if entry is None or (
                entry.display_name.lower() not in stmt_lower
                and entry.short_name.lower() not in stmt_lower
            ):
                return False

    # If the hypothesis was an equality or predicate with multi-char identifiers, check overlap
    if not salient and not custom_macros:
        idents = [
            tok for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]{3,}", hyp)
            if tok.lower()
            not in {
                "real", "complex", "nat", "int", "rat", "prop", "type", "forall", "exists",
                "finset", "set", "filter", "measuretheory", "arithmeticfunction",
                "riemannzeta", "dirichletcharacter", "vonmangoldt", "lfunction",
            }
        ]
        if idents and not any(op in hyp for op in ("<", ">", "≤", "≥", "≠", "!=")):
            # Allow match either via identifier name or translated hyp_tex tokens
            matched = False
            for ident in idents:
                tail = ident.rsplit(".", 1)[-1].lower()
                if tail in stmt_lower or tail.replace("_", "") in stmt_lower.replace("\\", "").replace("_", ""):
                    matched = True
                    break
            if not matched and hyp_tex_lower not in stmt_lower:
                return False

    return True


def _transitive_deps_check(
    conn: sqlite3.Connection,
    start_id: int,
    targets: set[int],
    adj_cache: dict[int, list[int]],
    closure_cache: dict[int, set[int]],
    *,
    max_visit: int = 250000,
) -> set[int]:
    """Return the subset of `targets` reachable from `start_id` in the Lean dependency DAG."""
    if not targets:
        return set()
    if start_id in closure_cache:
        return targets & closure_cache[start_id]

    visited: set[int] = set()
    found: set[int] = set()
    queue: deque[int] = deque([start_id])
    complete = True

    while queue:
        if len(visited) >= max_visit:
            complete = False
            break
        cur = queue.popleft()
        if cur not in adj_cache:
            rows = conn.execute(
                "SELECT DISTINCT dst_id FROM edges WHERE src_id = ?",
                (cur,),
            ).fetchall()
            adj_cache[cur] = [int(r[0]) for r in rows]
        for nxt in adj_cache[cur]:
            if nxt not in visited:
                visited.add(nxt)
                if nxt in targets:
                    found.add(nxt)
                    if len(found) == len(targets):
                        # All cited targets verified in DAG — early exit!
                        return found
                queue.append(nxt)

    if complete:
        closure_cache[start_id] = visited
    return found


def audit_latex(
    db: DbHandle,
    latex_source: str | Path,
    *,
    output_json: str | Path | None = None,
    output_md: str | Path | None = None,
    bottleneck_threshold: float | None = None,
) -> dict[str, Any]:
    """Audit generated LaTeX statements and proof citations against the SQLite Lean graph."""
    if isinstance(latex_source, Path) or (
        isinstance(latex_source, str)
        and "\n" not in latex_source
        and Path(latex_source).exists()
    ):
        tex_text = Path(latex_source).read_text(encoding="utf-8")
        source_label = str(latex_source)
    else:
        tex_text = str(latex_source)
        source_label = "<inline>"

    with open_db(db, readonly=False) as conn:
        use_reach = has_reachable_metrics(conn)
        registry = SymbolRegistry.load_from_db(conn)

        # 1. Extract all \leanlink{const} occurrences
        all_link_matches = list(_LEANLINK_RE.finditer(tex_text))
        unique_links = sorted({m.group(1).strip() for m in all_link_matches})

        decl_by_name: dict[str, dict[str, Any]] = {}
        if unique_links:
            # Query in batches of 500 to stay well below SQLite variable limits
            for i in range(0, len(unique_links), 500):
                batch = unique_links[i : i + 500]
                ph = ",".join("?" for _ in batch)
                rows = query_all(
                    conn,
                    f"""
                    SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.is_mathlib,
                           d.is_bookkeeping,
                           COALESCE(m.reachable, 1) AS reachable,
                           COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score
                    FROM declarations d
                    LEFT JOIN metrics m ON m.decl_id = d.id
                    WHERE d.name IN ({ph})
                    """,
                    tuple(batch),
                )
                for r in rows:
                    decl_by_name[str(r["name"])] = r

        unknown_leanlinks: list[dict[str, Any]] = []
        unreachable_leanlinks: list[dict[str, Any]] = []
        seen_unknown: set[str] = set()
        seen_unreach: set[str] = set()

        for m in all_link_matches:
            const = m.group(1).strip()
            line_no = _line_of_offset(tex_text, m.start())
            rec = decl_by_name.get(const)
            if rec is None:
                if const not in seen_unknown:
                    seen_unknown.add(const)
                    unknown_leanlinks.append({"constant": const, "line": line_no})
            elif use_reach and int(rec["reachable"] or 0) == 0:
                if const not in seen_unreach:
                    seen_unreach.add(const)
                    unreachable_leanlinks.append({"constant": const, "line": line_no})

        # Determine bottleneck threshold for omitted-dependency check
        eff_threshold = bottleneck_threshold
        top_global_bn_ids: set[int] = set()
        if use_reach:
            top_bn_rows = query_all(
                conn,
                """
                SELECT d.id, m.bottleneck_score
                FROM declarations d
                JOIN metrics m ON m.decl_id = d.id
                WHERE m.reachable = 1
                  AND d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                  AND m.bottleneck_score > 0
                ORDER BY m.bottleneck_score DESC
                LIMIT 200
                """,
            )
            scores = [float(r["bottleneck_score"]) for r in top_bn_rows]
            top_global_bn_ids = {int(r["id"]) for r in top_bn_rows[:20]}
            if eff_threshold is None:
                if scores:
                    # Top quartile cutoff among positive bottleneck scores, floored at 1.0
                    idx = max(0, min(len(scores) - 1, len(scores) // 4))
                    eff_threshold = max(1.0, scores[idx])
                else:
                    eff_threshold = 1e9
        else:
            if eff_threshold is None:
                eff_threshold = 1e9

        # 2 & 3. Audit theorem blocks + paired proofs
        invented_citations: list[dict[str, Any]] = []
        omitted_bottlenecks: list[dict[str, Any]] = []
        dropped_hypotheses: list[dict[str, Any]] = []

        adj_cache: dict[int, list[int]] = {}
        closure_cache: dict[int, set[int]] = {}
        audited_theorems = 0
        audited_proofs = 0

        for m in _THEOREM_BLOCK_RE.finditer(tex_text):
            env_name = m.group(1)
            stmt_body = m.group(2) or ""
            proof_body = m.group(3)
            block_line = _line_of_offset(tex_text, m.start())

            stmt_links = _LEANLINK_RE.findall(stmt_body)
            if not stmt_links:
                continue
            thm_name = stmt_links[0].strip()
            thm_rec = decl_by_name.get(thm_name)
            if thm_rec is None:
                continue
            audited_theorems += 1
            thm_id = int(thm_rec["id"])

            # 3. Statement / hypothesis fidelity check
            stmt_for_hyp = _strip_theorem_header_for_stmt_check(stmt_body)
            raw_sig = str(thm_rec.get("type_sig") or "")
            if r"\cdots" in stmt_for_hyp and len(raw_sig) > 480:
                raw_sig = raw_sig[:480]
            hyps = _extract_lean_hypotheses(raw_sig)
            missing_hyps = [
                h for h in hyps
                if not _hypothesis_present_in_latex(h, stmt_for_hyp, registry)
            ]
            if missing_hyps:
                dropped_hypotheses.append(
                    {
                        "theorem": thm_name,
                        "env": env_name,
                        "line": block_line,
                        "missing_hypotheses": missing_hyps[:5],
                    }
                )

            # 2. Proof DAG dependency check
            if proof_body is not None:
                audited_proofs += 1
                proof_links = [c.strip() for c in _LEANLINK_RE.findall(proof_body)]

                # Collect existing cited IDs for fast early-exit DAG reachability check
                cited_pairs: list[tuple[str, int]] = []
                cited_ids: set[int] = set()
                for cited_name in proof_links:
                    if cited_name == thm_name:
                        continue
                    cited_rec = decl_by_name.get(cited_name)
                    if cited_rec is None:
                        invented_citations.append(
                            {
                                "theorem": thm_name,
                                "cited": cited_name,
                                "line": block_line,
                                "reason": "Cited constant does not exist in Lean graph",
                            }
                        )
                        continue
                    cid = int(cited_rec["id"])
                    cited_ids.add(cid)
                    cited_pairs.append((cited_name, cid))

                reachable_cited = _transitive_deps_check(
                    conn, thm_id, cited_ids, adj_cache, closure_cache
                )
                for cited_name, cid in cited_pairs:
                    if cid not in reachable_cited:
                        invented_citations.append(
                            {
                                "theorem": thm_name,
                                "cited": cited_name,
                                "line": block_line,
                                "reason": "Cited constant is not in the Lean dependency DAG of this theorem",
                            }
                        )

                # Check if any high-bottleneck direct non-bookkeeping dependency was omitted
                direct_rows = query_all(
                    conn,
                    """
                    SELECT DISTINCT d.id, d.name, d.kind,
                                    COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score
                    FROM edges e
                    JOIN declarations d ON d.id = e.dst_id
                    LEFT JOIN metrics m ON m.decl_id = d.id
                    WHERE e.src_id = ?
                      AND d.id != ?
                      AND d.is_mathlib = 0
                      AND d.is_bookkeeping = 0
                      AND d.kind IN ('theorem', 'lemma', 'axiom')
                    """,
                    (thm_id, thm_id),
                )
                for dr in direct_rows:
                    did = int(dr["id"])
                    bscore = float(dr["bottleneck_score"] or 0.0)
                    is_high_bn = (bscore >= eff_threshold) or (
                        did in top_global_bn_ids and bscore > 0
                    )
                    if is_high_bn and did not in cited_ids:
                        omitted_bottlenecks.append(
                            {
                                "theorem": thm_name,
                                "missing_dependency": str(dr["name"]),
                                "bottleneck_score": round(bscore, 3),
                                "line": block_line,
                            }
                        )

        # 4. Symbol drift check (custom macros used in body outside registry + preamble defs)
        preamble_split = tex_text.split(r"\begin{document}", 1)
        preamble = preamble_split[0] if len(preamble_split) == 2 else ""
        body = preamble_split[1] if len(preamble_split) == 2 else tex_text
        body_offset = tex_text.find(r"\begin{document}") if len(preamble_split) == 2 else 0

        declared_in_preamble = set(_MACRO_DEF_RE.findall(preamble))
        registered_macros = {m.lstrip("\\") for m in registry.macros_set()}
        allowed_macros = _STANDARD_TEX_MACROS | declared_in_preamble | registered_macros

        # Remove comments and \detokenize{...} arguments before scanning macros
        body_no_comments_lines: list[str] = []
        for ln in body.splitlines():
            body_no_comments_lines.append(re.sub(r"(?<!\\)%.*$", "", ln))
        body_clean = "\n".join(body_no_comments_lines)
        body_clean = re.sub(r"\\detokenize\{[^}]*\}", "", body_clean)
        body_clean = re.sub(r"\\leanlink(?:\[[^\]]*\])?\{[^}]*\}", "", body_clean)
        body_clean = re.sub(r"\\leanmod\{[^}]*\}", "", body_clean)

        symbol_drift: list[dict[str, Any]] = []
        seen_drift: set[str] = set()
        for mm in _MACRO_USE_RE.finditer(body_clean):
            cmd = mm.group(1)
            if cmd not in allowed_macros and cmd not in seen_drift:
                seen_drift.add(cmd)
                symbol_drift.append(
                    {
                        "macro": f"\\{cmd}",
                        "line": _line_of_offset(tex_text, body_offset + mm.start()),
                        "reason": "Macro not defined in preamble or global symbol registry",
                    }
                )

        # 5. Bookkeeping leaks check
        bookkeeping_leaks = detect_bookkeeping_leaks(tex_text)

        # Compute overall fidelity score & pass flag
        total_errors = (
            len(unknown_leanlinks)
            + len(unreachable_leanlinks)
            + len(invented_citations)
            + len(omitted_bottlenecks)
            + len(dropped_hypotheses)
            + len(symbol_drift)
            + len(bookkeeping_leaks)
        )
        denom = max(1, len(unique_links) + audited_theorems + audited_proofs)
        penalty = (
            len(unknown_leanlinks) * 1.5
            + len(unreachable_leanlinks) * 1.0
            + len(invented_citations) * 2.0
            + len(omitted_bottlenecks) * 1.0
            + len(dropped_hypotheses) * 1.5
            + len(symbol_drift) * 0.75
            + len(bookkeeping_leaks) * 0.75
        )
        fidelity_score = round(max(0.0, 1.0 - min(1.0, penalty / denom)), 4)

        report: dict[str, Any] = {
            "source": source_label,
            "passed": total_errors == 0,
            "fidelity_score": fidelity_score,
            "summary": {
                "total_leanlinks": len(all_link_matches),
                "unique_leanlinks": len(unique_links),
                "audited_theorems": audited_theorems,
                "audited_proofs": audited_proofs,
                "unknown_leanlinks": len(unknown_leanlinks),
                "unreachable_leanlinks": len(unreachable_leanlinks),
                "invented_citations": len(invented_citations),
                "omitted_bottlenecks": len(omitted_bottlenecks),
                "dropped_hypotheses": len(dropped_hypotheses),
                "symbol_drift": len(symbol_drift),
                "bookkeeping_leaks": len(bookkeeping_leaks),
                "total_issues": total_errors,
            },
            "unknown_leanlinks": unknown_leanlinks,
            "unreachable_leanlinks": unreachable_leanlinks,
            "invented_citations": invented_citations,
            "omitted_bottlenecks": omitted_bottlenecks,
            "dropped_hypotheses": dropped_hypotheses,
            "symbol_drift": symbol_drift,
            "bookkeeping_leaks": bookkeeping_leaks,
        }

    if output_json is not None:
        out_j = Path(output_json)
        out_j.parent.mkdir(parents=True, exist_ok=True)
        out_j.write_text(json.dumps(report, indent=2), encoding="utf-8")

    if output_md is not None:
        out_m = Path(output_md)
        out_m.parent.mkdir(parents=True, exist_ok=True)
        out_m.write_text(format_audit_markdown(report), encoding="utf-8")

    return report


def format_audit_markdown(report: dict[str, Any]) -> str:
    """Render a structured audit report as concise GitHub-flavored Markdown."""
    s = report.get("summary", {})
    status = "PASS" if report.get("passed") else "FAIL"
    lines = [
        f"# Proof Exposition Audit Report ({status})",
        "",
        f"- **Source:** `{report.get('source', '<unknown>')}`",
        f"- **Fidelity Score:** `{report.get('fidelity_score', 0.0):.4f}`",
        f"- **Verified `\\leanlink` anchors:** {s.get('unique_leanlinks', 0)} unique ({s.get('total_leanlinks', 0)} total)",
        f"- **Audited theorems / proofs:** {s.get('audited_theorems', 0)} / {s.get('audited_proofs', 0)}",
        "",
        "## Issue Summary",
        "",
        "| Check | Issues |",
        "|---|---:|",
        f"| Unknown `\\leanlink` constants | {s.get('unknown_leanlinks', 0)} |",
        f"| Unreachable (dead) `\\leanlink` constants | {s.get('unreachable_leanlinks', 0)} |",
        f"| Invented / non-DAG proof citations | {s.get('invented_citations', 0)} |",
        f"| Omitted high-bottleneck dependencies | {s.get('omitted_bottlenecks', 0)} |",
        f"| Potential dropped hypotheses | {s.get('dropped_hypotheses', 0)} |",
        f"| Symbol drift (unregistered macros) | {s.get('symbol_drift', 0)} |",
        f"| Lean bookkeeping leaks in prose | {s.get('bookkeeping_leaks', 0)} |",
        "",
    ]

    def _section(title: str, items: list[dict[str, Any]], fmt: Any) -> None:
        if not items:
            return
        lines.append(f"## {title}")
        lines.append("")
        for it in items[:25]:
            lines.append(f"- {fmt(it)}")
        if len(items) > 25:
            lines.append(f"- ... and {len(items) - 25} more.")
        lines.append("")

    _section(
        "Unknown Lean Links",
        report.get("unknown_leanlinks", []),
        lambda it: f"Line {it['line']}: `{it['constant']}` not found in database",
    )
    _section(
        "Unreachable Lean Links",
        report.get("unreachable_leanlinks", []),
        lambda it: f"Line {it['line']}: `{it['constant']}` is unreachable from root theorem",
    )
    _section(
        "Invented / Non-DAG Citations",
        report.get("invented_citations", []),
        lambda it: f"Line {it['line']}: proof of `{it['theorem']}` cites `{it['cited']}` ({it['reason']})",
    )
    _section(
        "Omitted High-Bottleneck Dependencies",
        report.get("omitted_bottlenecks", []),
        lambda it: f"Line {it['line']}: proof of `{it['theorem']}` omits `{it['missing_dependency']}` (score={it['bottleneck_score']})",
    )
    _section(
        "Potential Dropped Hypotheses",
        report.get("dropped_hypotheses", []),
        lambda it: f"Line {it['line']}: `{it['theorem']}` may drop hypotheses: {', '.join(it['missing_hypotheses'])}",
    )
    _section(
        "Symbol Drift",
        report.get("symbol_drift", []),
        lambda it: f"Line {it['line']}: unregistered macro `{it['macro']}`",
    )
    _section(
        "Bookkeeping Leaks",
        report.get("bookkeeping_leaks", []),
        lambda it: f"Line {it['line']} [{it['kind']}]: `{it['match']}`",
    )

    return "\n".join(lines).strip() + "\n"
