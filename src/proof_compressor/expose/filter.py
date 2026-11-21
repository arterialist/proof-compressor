"""Bookkeeping & triviality filter and mathematical proof-idiom extractor."""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass
from typing import Any, Iterable

from proof_compressor.expose._db import (
    DbHandle,
    get_cluster_hierarchy,
    has_reachable_metrics,
    open_db,
    query_all,
)

# ---------------------------------------------------------------------------
# Bookkeeping classification rules
# ---------------------------------------------------------------------------

_BOOKKEEPING_KINDS = frozenset({"instance"})

_BOOKKEEPING_NAME_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "coercion",
        re.compile(
            r"(?:^|[._])(coe|cast|ofNat|toNat|ofReal|toReal|ofInt|toInt|ofRat|toRat|"
            r"coe_eq|cast_eq|norm_cast|push_cast|coe_add|coe_mul|coe_sub|coe_neg|"
            r"coe_zero|coe_one|coe_inv|coe_div|coe_pow|coe_sum|coe_prod|"
            r"map_add|map_mul|map_sub|map_neg|map_zero|map_one|map_sum|map_prod|"
            r"toFun_eq_coe|mk_coe|ext_iff)(?:$|[._])",
            re.IGNORECASE,
        ),
    ),
    (
        "order_glue",
        re.compile(
            r"(?:^|[._])(lt_or_gt|le_or_gt|lt_or_le|le_total|trichotom|"
            r"ne_of_lt|ne_of_gt|le_of_lt|pos_of_gt|nonneg_of_pos|"
            r"lt_trans_aux|le_trans_aux|max_comm|min_comm|abs_nonneg|"
            r"zero_lt_one|zero_le_one|one_pos|two_pos|add_pos|mul_pos|"
            r"sub_pos|sub_nonneg|div_pos|inv_pos|sq_nonneg|pow_pos|pow_nonneg)(?:$|[._])",
            re.IGNORECASE,
        ),
    ),
    (
        "typeclass_plumbing",
        re.compile(
            r"(?:^|[._])(decidable|decidableEq|decidablePred|decidableRel|"
            r"measurable|aemeasurable|stronglyMeasurable|aeStronglyMeasurable|"
            r"integrable|locallyIntegrable|continuous|continuousOn|continuousAt|"
            r"finite|fintype|countable|nonempty|inhabited|isEmpty|neZero|nontrivial|"
            r"subsingleton|unique|inst[A-Z]|hasMem|hasCoe|hasLift|inferInstance)(?:$|[._])",
            re.IGNORECASE,
        ),
    ),
    (
        "simp_helper",
        re.compile(
            r"(?:^|[._])(aux\d*|helper\d*|simp\d*|rw\d*|eq_self|rfl|"
            r"def_eq|unfold|mk_eq|eta|beta|congr_arg|congr_fun|subst|"
            r"mem_iff|mem_setOf|mem_finset|mem_range|mem_univ|card_eq|"
            r"finset_sum_congr|sum_congr|prod_congr|integral_congr)(?:$|[._])",
            re.IGNORECASE,
        ),
    ),
)

_BOOKKEEPING_TYPE_TARGETS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "typeclass_plumbing",
        re.compile(
            r"\b(Decidable(?:Eq|Pred|Rel)?|Measurable(?:Set|Space)?|"
            r"AEMeasurable|AEStronglyMeasurable|StronglyMeasurable|"
            r"Integrable|LocallyIntegrable|Continuous(?:On|At|WithinAt)?|"
            r"Finite|Fintype|Countable|Nonempty|Inhabited|IsEmpty|NeZero|"
            r"Nontrivial|Subsingleton|TopologicalSpace|MeasurableSpace|"
            r"NormedAddCommGroup|Module|Algebra|CommRing|Field|Group)\b"
        ),
    ),
    (
        "coercion",
        re.compile(r"(?:\bCoe\b|\bCoeOut\b|\bCoeFun\b|\bCoeSort\b|\bNat\.cast\b|\bInt\.cast\b|\bRat\.cast\b|\bComplex\.ofReal\b)"),
    ),
)

# High-value mathematical keywords that override weak bookkeeping heuristics
_STRONG_MATH_KEYWORDS = re.compile(
    r"\b(riemann|zeta|hypothesis|grh|lfunction|l_function|dirichlet|"
    r"automorphic|theta|bessel|whittaker|seesaw|trace_formula|rtf|"
    r"stepanov|determinant|wronskian|vandermonde|slope|bost|arakelov|"
    r"iwasawa|selmer|vandiver|cohomology|galois|hecke|langlands|"
    r"rankin|selberg|explicit_formula|guinand|weil|positivity|"
    r"zero_free|nonvanishing|non_vanishing|functional_equation|"
    r"analytic_continuation|euler_product|parseval|plancherel|"
    r"cauchy_schwarz|mellin|fourier|spectral|ramanujan|petersson|"
    r"cusp|eisenstein|unitary|symplectic|metaplectic|tamagawa|"
    r"fundamental_lemma|orbital_integral|main_theorem|pillar)\b",
    re.IGNORECASE,
)


@dataclass(slots=True)
class BookkeepingClassification:
    """Result of classifying a Lean declaration as mathematical vs bookkeeping."""

    is_bookkeeping: bool
    category: str
    reason: str
    confidence: float

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _extract_conclusion(type_sig: str) -> str:
    """Heuristically extract the target conclusion of a Lean type signature."""
    if not type_sig:
        return ""
    text = " ".join(type_sig.split())
    # Walk from right past top-level arrows / commas outside parens/brackets
    depth = 0
    last_sep = -1
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            depth = max(0, depth - 1)
        elif depth == 0:
            if ch in (",", "→"):
                last_sep = i
            elif text[i : i + 2] == "->":
                last_sep = i + 1
                i += 1
        i += 1
    if last_sep >= 0 and last_sep + 1 < n:
        return text[last_sep + 1 :].strip()
    return text


def classify_bookkeeping(
    name: str,
    kind: str = "",
    type_sig: str = "",
    body_loc: int = 0,
    docstring: str = "",
    existing_flag: int = 0,
) -> BookkeepingClassification:
    """Classify whether a Lean declaration is routine bookkeeping/glue."""
    short = name.rsplit(".", 1)[-1] if name else ""
    kind_l = (kind or "").strip().lower()
    type_s = type_sig or ""
    doc_s = docstring or ""

    # Strong mathematical definitions/theorems with non-trivial bodies are kept
    name_spaced = re.sub(r"[._/]+", " ", re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", name))
    has_strong_math = bool(
        _STRONG_MATH_KEYWORDS.search(name)
        or _STRONG_MATH_KEYWORDS.search(name_spaced)
        or _STRONG_MATH_KEYWORDS.search(doc_s)
    )

    if kind_l in _BOOKKEEPING_KINDS:
        return BookkeepingClassification(
            is_bookkeeping=True,
            category="typeclass_plumbing",
            reason="Lean typeclass instance declaration",
            confidence=0.98,
        )

    # Check conclusion type targets (e.g., `... → Measurable f`, `... → Decidable P`)
    conclusion = _extract_conclusion(type_s)
    if kind_l in ("theorem", "lemma", "def", "abbrev", ""):
        for cat, pat in _BOOKKEEPING_TYPE_TARGETS:
            if conclusion and pat.match(conclusion):
                if not (has_strong_math and body_loc >= 40):
                    return BookkeepingClassification(
                        is_bookkeeping=True,
                        category=cat,
                        reason=f"Conclusion asserts routine {cat.replace('_', ' ')} predicate",
                        confidence=0.92,
                    )

    # Check declaration naming patterns (normalize camelCase to snake_case for matching)
    short_norm = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", short)
    for cat, pat in _BOOKKEEPING_NAME_PATTERNS:
        if pat.search(short) or pat.search(short_norm):
            if has_strong_math and body_loc >= 30:
                continue
            return BookkeepingClassification(
                is_bookkeeping=True,
                category=cat,
                reason=f"Declaration name '{short}' matches {cat.replace('_', ' ')} pattern",
                confidence=0.88,
            )

    # Very short trivial arithmetic / definitional lemmas
    if kind_l in ("lemma", "theorem") and 0 < body_loc <= 3 and not has_strong_math:
        if re.search(
            r"(?:^|[._])(pos|neg|nonneg|ne_zero|zero|one|add|sub|mul|div|le|lt|eq|iff|comm|assoc|symm)(?:$|[._])",
            short,
            re.IGNORECASE,
        ):
            return BookkeepingClassification(
                is_bookkeeping=True,
                category="trivial_arithmetic",
                reason=f"Short ({body_loc} LOC) elementary algebraic/order rewrite",
                confidence=0.82,
            )

    # Respect upstream extractor flag if no strong mathematical signal overrides it
    if existing_flag and not (has_strong_math and body_loc >= 25):
        return BookkeepingClassification(
            is_bookkeeping=True,
            category="extractor_flagged",
            reason="Flagged as bookkeeping during ingestion",
            confidence=0.75,
        )

    return BookkeepingClassification(
        is_bookkeeping=False,
        category="mathematical",
        reason="Substantive mathematical declaration",
        confidence=0.90 if has_strong_math else 0.70,
    )


def tag_bookkeeping(
    db: DbHandle,
    *,
    update_db: bool = True,
    reachable_only: bool = False,
) -> dict[str, Any]:
    """Classify declarations in SQLite and optionally update `declarations.is_bookkeeping`."""
    with open_db(db) as conn:
        use_reach = reachable_only and has_reachable_metrics(conn)
        if use_reach:
            rows = query_all(
                conn,
                """
                SELECT d.id, d.name, d.kind, d.type_sig, d.body_loc, d.docstring, d.is_bookkeeping
                FROM declarations d
                JOIN metrics m ON m.decl_id = d.id
                WHERE m.reachable = 1 AND d.is_mathlib = 0
                """,
            )
        else:
            rows = query_all(
                conn,
                """
                SELECT id, name, kind, type_sig, body_loc, docstring, is_bookkeeping
                FROM declarations
                WHERE is_mathlib = 0
                """,
            )

        counts_by_category: dict[str, int] = {}
        updates: list[tuple[int, int]] = []
        bookkeeping_count = 0
        mathematical_count = 0

        for r in rows:
            res = classify_bookkeeping(
                name=r["name"] or "",
                kind=r["kind"] or "",
                type_sig=r["type_sig"] or "",
                body_loc=int(r["body_loc"] or 0),
                docstring=r["docstring"] or "",
                existing_flag=int(r["is_bookkeeping"] or 0),
            )
            counts_by_category[res.category] = counts_by_category.get(res.category, 0) + 1
            new_flag = 1 if res.is_bookkeeping else 0
            if new_flag:
                bookkeeping_count += 1
            else:
                mathematical_count += 1
            if new_flag != int(r["is_bookkeeping"] or 0):
                updates.append((new_flag, int(r["id"])))

        if update_db and updates:
            conn.executemany(
                "UPDATE declarations SET is_bookkeeping = ? WHERE id = ?",
                updates,
            )
            conn.commit()

        return {
            "total_evaluated": len(rows),
            "bookkeeping_count": bookkeeping_count,
            "mathematical_count": mathematical_count,
            "updated_rows": len(updates) if update_db else 0,
            "by_category": counts_by_category,
        }


# ---------------------------------------------------------------------------
# Bookkeeping leak detector for prose / LaTeX
# ---------------------------------------------------------------------------

_PROSE_LEAK_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "finset_leak",
        re.compile(r"\b(Finset(?:\.\w+)?|Fintype|Multiset|List\.map|List\.fold)\b"),
    ),
    (
        "typeclass_leak",
        re.compile(
            r"\b(Decidable(?:Eq|Pred|Rel)?|Measurable(?:Space)?|AEMeasurable|"
            r"StronglyMeasurable|Inhabited|Subsingleton|NeZero|typeclass|instance synthesis)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "coercion_leak",
        re.compile(
            r"\b(coercion|cast(?:ing)?\s+(?:from|to|between)|norm_cast|push_cast|"
            r"Complex\.ofReal|Nat\.cast|Int\.cast|Subtype\.val)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "tactic_leak",
        re.compile(
            r"\b(simp\s+lemma|norm_num|linarith|nlinarith|ring_nf|omega\s+tactic|"
            r"by\s+rfl|definitional\s+equality|beta-reduction)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "trivial_order_leak",
        re.compile(
            r"(?:because|since)\s+the\s+reals?\s+(?:are|is)\s+totally\s+ordered|"
            r"\border\s+trichotomy\b|\btrivial\s+monotonicity\b",
            re.IGNORECASE,
        ),
    ),
)


def detect_bookkeeping_leaks(text: str) -> list[dict[str, Any]]:
    """Scan generated mathematical prose for leaked Lean bookkeeping artifacts."""
    leaks: list[dict[str, Any]] = []
    if not text:
        return leaks

    # Strip \leanlink{...}, \leanmod{...}, and LaTeX comments before scanning prose
    lines = text.splitlines()
    in_appendix = False
    for line_no, raw_line in enumerate(lines, start=1):
        stripped = raw_line.strip()
        if stripped.startswith("%"):
            continue
        if re.search(r"\\appendix\b", stripped):
            in_appendix = True
        if in_appendix:
            # Appendix tables legitimately display Lean symbol names and audit stats
            continue

        # Remove \leanlink{...} and \texttt{...} identifiers from prose scan
        cleaned = re.sub(r"\\leanlink(?:\[[^\]]*\])?\{[^}]*\}", " ", stripped)
        cleaned = re.sub(r"\\leanmod\{[^}]*\}", " ", cleaned)
        cleaned = re.sub(r"\\newcommand\{[^}]*\}.*$", " ", cleaned)
        cleaned = re.sub(r"\\providecommand\{[^}]*\}.*$", " ", cleaned)
        if not cleaned.strip():
            continue

        for kind, pat in _PROSE_LEAK_PATTERNS:
            for m in pat.finditer(cleaned):
                leaks.append(
                    {
                        "line": line_no,
                        "kind": kind,
                        "match": m.group(0),
                        "snippet": stripped[:140],
                    }
                )
    return leaks


# ---------------------------------------------------------------------------
# Mathematical Proof Idiom Extractor
# ---------------------------------------------------------------------------

_PROOF_IDIOMS: tuple[tuple[str, str, tuple[tuple[str, float], ...]], ...] = (
    (
        "determinant / Stepanov",
        "Auxiliary polynomial / determinant method bounds (Stepanov-Bombieri / Wronskian)",
        (
            (r"\bstepanov\b", 4.0),
            (r"\bdeterminant(?:_method)?\b", 2.5),
            (r"\bwronskian\b", 3.0),
            (r"\bvandermonde\b", 2.5),
            (r"\bauxiliary_poly|aux_poly|vanishing_order|multiplicity_bound\b", 2.5),
            (r"\binterpolation\b", 1.5),
            (r"\bsiegel_lemma\b", 3.0),
        ),
    ),
    (
        "iterated theta lift",
        "Howe duality, Weil representations, and iterated theta correspondences",
        (
            (r"\btheta_?lift\b", 4.0),
            (r"\bhowe_?duality\b", 4.0),
            (r"\bweil_?rep(?:resentation)?\b", 3.5),
            (r"\bmetaplectic\b", 3.0),
            (r"\brallis\b", 3.5),
            (r"\bdoubling_?method\b", 3.5),
            (r"\bdual_?pair\b", 3.0),
            (r"\btheta_?(?:kernel|series|function|correspondence)\b", 2.5),
        ),
    ),
    (
        "seesaw / Bessel period",
        "Seesaw dual pairs and Bessel / Fourier-Jacobi period identities",
        (
            (r"\bseesaw\b", 4.0),
            (r"\bbessel(?:_?period|_?model|_?function)?\b", 3.5),
            (r"\bfourier_?jacobi\b", 3.5),
            (r"\bggp\b|\bgan_?gross_?prasad\b", 4.0),
            (r"\bwhittaker(?:_?period|_?model|_?function)?\b", 2.8),
            (r"\bperiod_?integral\b", 2.5),
        ),
    ),
    (
        "relative trace formula",
        "Relative / Arthur-Selberg trace formula, orbital integrals, and smooth transfer",
        (
            (r"\brelative_?trace|rtf\b", 4.0),
            (r"\btrace_?formula\b", 3.5),
            (r"\borbital_?integral\b", 3.5),
            (r"\bfundamental_?lemma\b", 3.5),
            (r"\bsmooth_?transfer\b", 3.5),
            (r"\bjacquet_?rallis\b", 4.0),
            (r"\barthur_?selberg\b", 3.5),
            (r"\bspectral_?side|geometric_?side\b", 3.0),
        ),
    ),
    (
        "Cauchy-Schwarz / Parseval",
        "L^2 spectral / harmonic bounds via Cauchy-Schwarz, Parseval, and Plancherel",
        (
            (r"\bcauchy_?schwarz\b", 3.5),
            (r"\bparseval\b", 3.5),
            (r"\bplancherel\b", 3.5),
            (r"\bspectral_?expansion\b", 3.0),
            (r"\bmellin\b", 2.5),
            (r"\bfourier_?(?:transform|inversion)\b", 2.0),
            (r"\binner_?product|hilbert_?space|l2_?norm\b", 1.5),
        ),
    ),
    (
        "Bost slope inequality",
        "Arakelov geometry, Hermitian vector bundles, and Bost slope inequalities",
        (
            (r"\bbost\b", 4.0),
            (r"\bslope_?ineq(?:uality)?|minimal_?slope|maximal_?slope\b", 3.5),
            (r"\barakelov\b", 3.5),
            (r"\bharder_?narasimhan\b", 4.0),
            (r"\bhermitian_?(?:bundle|metric|vector)\b", 3.0),
            (r"\barithmetic_?degree|height_?bound\b", 2.5),
            (r"\bminkowski_?(?:bound|convex|lattice)\b", 2.2),
        ),
    ),
    (
        "Iwasawa tower",
        "Cyclotomic Z_p-extensions, Iwasawa algebras, and Selmer modules",
        (
            (r"\biwasawa\b", 4.0),
            (r"\bcyclotomic_?tower|zp_?extension\b", 3.5),
            (r"\bselmer\b", 3.0),
            (r"\bmain_?conjecture\b", 3.5),
            (r"\bcharacteristic_?ideal\b", 3.0),
            (r"\bmu_?invariant|lambda_?invariant\b", 3.0),
            (r"\bpadic_?l_?function\b", 3.0),
        ),
    ),
    (
        "Vandiver / cohomology",
        "Galois / étale cohomology, class groups, Kummer theory, and Euler systems",
        (
            (r"\bvandiver\b", 4.0),
            (r"\bgalois_?cohomology|etale_?cohomology|group_?cohomology\b", 3.5),
            (r"\bcohomology\b", 2.2),
            (r"\bkummer\b", 2.8),
            (r"\bclass_?group|ideal_?class\b", 2.5),
            (r"\beuler_?system|kolyvagin\b", 3.5),
            (r"\bgreenberg\b", 3.0),
            (r"\bgalois_?rep(?:resentation)?\b", 2.5),
        ),
    ),
    (
        "explicit formula / Guinand-Weil",
        "Explicit formulas, Weil positivity, zero-free regions, and contour integration",
        (
            (r"\bguinand\b", 4.0),
            (r"\bweil_?(?:explicit|positivity|distribution)\b", 3.8),
            (r"\bexplicit_?formula\b", 3.8),
            (r"\bzero_?free\b", 3.5),
            (r"\bperron\b", 3.0),
            (r"\bhadamard_?product\b", 3.0),
            (r"\bphragmen_?lindelof\b", 3.0),
            (r"\bcontour_?(?:shift|integral)\b", 2.5),
            (r"\bvon_?mangoldt|chebyshev|riemann_?zeta|riemann_?hypothesis\b", 2.0),
        ),
    ),
    (
        "L-function / Rankin-Selberg",
        "Automorphic L-functions, Rankin-Selberg integrals, functional equations, non-vanishing",
        (
            (r"\brankin_?selberg\b", 4.0),
            (r"\bl_?function|lfunction\b", 2.5),
            (r"\bfunctional_?eq(?:uation)?\b", 2.8),
            (r"\beuler_?product\b", 2.8),
            (r"\banalytic_?continuation\b", 2.5),
            (r"\bnon_?vanishing|nonvanishing\b", 2.8),
            (r"\bcompleted_?(?:zeta|l)\b", 2.5),
            (r"\bdirichlet_?character\b", 2.0),
        ),
    ),
    (
        "automorphic / spectral theory",
        "Automorphic representations, cusp forms, Hecke operators, and base change",
        (
            (r"\bautomorphic\b", 3.0),
            (r"\bcusp_?form|cuspidal\b", 3.0),
            (r"\beisenstein\b", 3.0),
            (r"\bhecke_?(?:operator|algebra|eigen)\b", 2.8),
            (r"\bsatake\b", 3.0),
            (r"\bramanujan_?petersson\b", 3.5),
            (r"\bbase_?change|functoriality|langlands\b", 3.0),
            (r"\bunitary_?group|symplectic_?group\b", 2.2),
        ),
    ),
    (
        "p-adic / local harmonic analysis",
        "Local p-adic groups, Bruhat-Tits buildings, Tamagawa measures, and adelic integrals",
        (
            (r"\bbruhat_?tits\b", 3.5),
            (r"\btamagawa\b", 3.5),
            (r"\badelic|adele|idele\b", 2.5),
            (r"\bpadic|p_adic\b", 2.0),
            (r"\bunramified|spherical_?function\b", 2.5),
            (r"\blocal_?langlands\b", 3.5),
        ),
    ),
    (
        "p-adic Hodge / Wach lattices",
        "p-adic Hodge theory, Wach modules, crystalline representations, and semistable reduction",
        (
            (r"\bwach\b", 4.0),
            (r"\bpadic_?hodge|p_?adic_?hodge\b", 4.0),
            (r"\bsemistable_?reduction\b", 3.5),
            (r"\bcrystalline\b", 2.8),
            (r"\bfontaine\b", 3.5),
            (r"\bprofinite_?cohomology\b", 3.0),
        ),
    ),
    (
        "Hermitian curvature / L^2 dbar",
        "Hermitian metrics, curvature positivity, and Hormander L^2 dbar estimates",
        (
            (r"\bhermitian_?curvature\b", 4.0),
            (r"\bl2_?dbar|dbar_?estimate|hormander\b", 4.0),
            (r"\bsharp_?restriction\b", 3.5),
            (r"\bspectral_?geometry\b", 3.0),
            (r"\bpositivity_?theory\b", 2.5),
        ),
    ),
    (
        "abelian varieties & heights",
        "Abelian varieties, Weil bounds, heights, theta divisors, and resolution of singularities",
        (
            (r"\babelian_?variet", 3.5),
            (r"\bweil_?bound\b", 3.5),
            (r"\bheights_?and_?theta\b", 3.5),
            (r"\bresolution_?of_?singularit", 3.5),
            (r"\bgraded_?weyl|weyl_?divisibility\b", 3.5),
            (r"\bcharacter_?box", 3.0),
        ),
    ),
    (
        "Harish-Chandra / real reductive groups",
        "Real reductive groups, Harish-Chandra modules, and GL_3 mean-square bounds",
        (
            (r"\bharish_?chandra\b", 4.0),
            (r"\breductive_?group\b", 3.0),
            (r"\breal_?group\b", 2.5),
            (r"\bgl3_?mean_?square|mean_?square\b", 3.5),
            (r"\bgamma_?factor\b", 3.0),
        ),
    ),
)

_COMPILED_IDIOMS: tuple[tuple[str, str, tuple[tuple[re.Pattern[str], float], ...]], ...] = tuple(
    (
        name,
        desc,
        tuple((re.compile(pat, re.IGNORECASE), weight) for pat, weight in patterns),
    )
    for name, desc, patterns in _PROOF_IDIOMS
)


def extract_proof_idioms(
    declarations: Iterable[dict[str, Any]],
    *,
    top_k: int = 4,
    min_score: float = 2.0,
) -> list[dict[str, Any]]:
    """Extract ranked mathematical proof-idiom tags from a set of declarations."""
    scores: dict[str, float] = {}
    evidence: dict[str, list[str]] = {}
    descriptions: dict[str, str] = {}

    for decl in declarations:
        name = str(decl.get("name") or "")
        short = str(decl.get("short_name") or name.rsplit(".", 1)[-1])
        module_path = str(decl.get("module_path") or decl.get("path") or "")
        docstring = str(decl.get("docstring") or "")
        type_sig = str(decl.get("type_sig") or "")

        # Normalize camelCase to both snake_case and space-separated tokens so both
        # compound (`theta_?lift`) and single-word (`\bbost\b`) boundary patterns match
        camel_norm = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", f"{module_path} {name}")
        spaced_norm = re.sub(r"[._/]+", " ", camel_norm)
        haystack = f"{camel_norm} {spaced_norm} {docstring} {type_sig[:400]}"
        weight_boost = 1.0 + min(2.0, float(decl.get("bottleneck_score") or 0.0) / 100.0)

        for idiom_name, desc, patterns in _COMPILED_IDIOMS:
            descriptions[idiom_name] = desc
            hit_score = 0.0
            for pat, w in patterns:
                if pat.search(haystack):
                    hit_score += w
            if hit_score > 0:
                scores[idiom_name] = scores.get(idiom_name, 0.0) + hit_score * weight_boost
                ev = evidence.setdefault(idiom_name, [])
                if short and short not in ev and len(ev) < 5:
                    ev.append(short)

    ranked = sorted(scores.items(), key=lambda kv: (-kv[1], kv[0]))
    results: list[dict[str, Any]] = []
    for idiom_name, score in ranked:
        if score < min_score:
            continue
        results.append(
            {
                "idiom": idiom_name,
                "description": descriptions[idiom_name],
                "score": round(score, 2),
                "evidence": evidence.get(idiom_name, []),
            }
        )
        if len(results) >= top_k:
            break
    return results


def extract_all_cluster_idioms(
    db: DbHandle,
    *,
    top_k: int = 3,
) -> dict[int, list[dict[str, Any]]]:
    """Compute mathematical proof-idiom tags for every cluster (sections and chapters)."""
    with open_db(db, readonly=False) as conn:
        _chapters, _sections, cluster_to_chapter = get_cluster_hierarchy(conn)
        rows = query_all(
            conn,
            """
            SELECT m.cluster_id, d.name, d.short_name, d.type_sig, d.docstring,
                   mod.path AS module_path, m.bottleneck_score
            FROM declarations d
            JOIN metrics m ON m.decl_id = d.id
            LEFT JOIN modules mod ON mod.id = d.module_id
            WHERE m.cluster_id IS NOT NULL
              AND d.is_mathlib = 0
              AND d.is_bookkeeping = 0
            ORDER BY m.cluster_id, m.bottleneck_score DESC
            """,
        )

    by_cluster: dict[int, list[dict[str, Any]]] = {}
    for r in rows:
        cid = int(r["cluster_id"])
        bucket = by_cluster.setdefault(cid, [])
        if len(bucket) < 400:
            bucket.append(r)
        # Also aggregate into parent chapter if distinct
        chap_id = cluster_to_chapter.get(cid)
        if chap_id is not None and chap_id != cid:
            chap_bucket = by_cluster.setdefault(chap_id, [])
            if len(chap_bucket) < 500:
                chap_bucket.append(r)

    return {
        cid: extract_proof_idioms(decls, top_k=top_k)
        for cid, decls in by_cluster.items()
    }
