"""Global symbol registry and Lean-to-LaTeX mathematical notation translator."""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass, field
from typing import Any

from proof_compressor.expose._db import (
    DbHandle,
    has_reachable_metrics,
    open_db,
    query_all,
)

# Declaration kinds eligible for the global symbol registry
SYMBOL_DECL_KINDS = ("def", "structure", "class", "inductive", "abbrev")

# Standard LaTeX / AMS commands we must NEVER overwrite with custom macros
_RESERVED_LATEX_MACROS = frozenset(
    {
        "a", "b", "c", "d", "H", "i", "j", "k", "l", "L", "o", "O", "P", "r", "S",
        "t", "u", "v", "AA", "AE", "OE", "Re", "Im", "Pr", "arg", "cos", "cot",
        "csc", "deg", "det", "dim", "div", "exp", "gcd", "hom", "inf", "int",
        "ker", "lg", "lim", "ln", "log", "max", "min", "mod", "prod", "sec",
        "sin", "sum", "sup", "tan", "to", "in", "ni", "le", "ge", "ne", "eq",
        "pm", "mp", "mid", "cap", "cup", "vee", "neg", "not", "bot", "top",
        "chi", "eta", "mu", "nu", "pi", "rho", "tau", "phi", "psi", "xi",
        "zeta", "beta", "iota", "alpha", "gamma", "delta", "kappa", "omega",
        "sigma", "theta", "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi",
        "Sigma", "Upsilon", "Phi", "Psi", "Omega", "mathbb", "mathcal", "mathrm",
        "mathbf", "mathfrak", "operatorname", "text", "texttt", "textbf", "emph",
        "section", "subsection", "theorem", "lemma", "proof", "definition",
        "proposition", "corollary", "remark", "leanlink", "leanmod", "label",
        "ref", "cite", "frac", "sqrt", "left", "right", "bigl", "bigr",
    }
)

# Domain-specific Lean identifier patterns -> (macro_base, math_rendering, display_name)
_DOMAIN_NOTATION_RULES: tuple[tuple[re.Pattern[str], str, str, str], ...] = (
    (re.compile(r"riemann_?zeta", re.I), "RiemannZeta", r"\zeta", "Riemann zeta function"),
    (re.compile(r"completed_?(?:riemann_?)?zeta", re.I), "CompletedZeta", r"\Lambda", "Completed zeta function"),
    (re.compile(r"dirichlet_?character", re.I), "DirichletChar", r"\chi", "Dirichlet character"),
    (re.compile(r"(?:dirichlet_?|automorphic_?|rankin_?selberg_?|standard_?)l_?function", re.I), "LFunc", r"L", "L-function"),
    (re.compile(r"von_?mangoldt", re.I), "VonMangoldt", r"\Lambda", "von Mangoldt function"),
    (re.compile(r"chebyshev_?psi", re.I), "ChebyshevPsi", r"\psi", "Chebyshev psi function"),
    (re.compile(r"theta_?lift", re.I), "ThetaLift", r"\Theta", "Theta lift"),
    (re.compile(r"theta_?(?:kernel|series|function)", re.I), "ThetaKernel", r"\theta", "Theta kernel"),
    (re.compile(r"weil_?rep(?:resentation)?", re.I), "WeilRep", r"\omega", "Weil representation"),
    (re.compile(r"bessel_?(?:period|model|function)", re.I), "BesselPeriod", r"\mathcal{B}", "Bessel period"),
    (re.compile(r"whittaker_?(?:period|model|function)", re.I), "WhittakerModel", r"\mathcal{W}", "Whittaker model"),
    (re.compile(r"fourier_?jacobi", re.I), "FourierJacobi", r"\mathcal{FJ}", "Fourier-Jacobi period"),
    (re.compile(r"unitary_?group", re.I), "UnitaryGroup", r"\mathrm{U}", "Unitary group"),
    (re.compile(r"special_?unitary", re.I), "SpecialUnitary", r"\mathrm{SU}", "Special unitary group"),
    (re.compile(r"symplectic_?group", re.I), "SymplecticGroup", r"\mathrm{Sp}", "Symplectic group"),
    (re.compile(r"metaplectic_?group", re.I), "MetaplecticGroup", r"\mathrm{Mp}", "Metaplectic group"),
    (re.compile(r"general_?linear", re.I), "GenLinear", r"\mathrm{GL}", "General linear group"),
    (re.compile(r"special_?linear", re.I), "SpecLinear", r"\mathrm{SL}", "Special linear group"),
    (re.compile(r"hecke_?(?:algebra|operator)", re.I), "HeckeAlg", r"\mathcal{H}", "Hecke algebra"),
    (re.compile(r"automorphic_?(?:form|rep)", re.I), "AutomorphicRep", r"\pi", "Automorphic representation"),
    (re.compile(r"cusp_?form", re.I), "CuspForm", r"\mathcal{A}_{\mathrm{cusp}}", "Cusp form"),
    (re.compile(r"eisenstein", re.I), "EisensteinSeries", r"E", "Eisenstein series"),
    (re.compile(r"cohomology", re.I), "CohomologyGrp", r"H^{\bullet}", "Cohomology group"),
    (re.compile(r"selmer", re.I), "SelmerGroup", r"\mathrm{Sel}", "Selmer group"),
    (re.compile(r"iwasawa", re.I), "IwasawaAlg", r"\Lambda_{\mathrm{Iw}}", "Iwasawa algebra"),
    (re.compile(r"galois", re.I), "GaloisGroup", r"\mathrm{Gal}", "Galois group"),
    (re.compile(r"bost_?slope|minimal_?slope|maximal_?slope|slope", re.I), "BostSlope", r"\widehat{\mu}", "Arakelov slope"),
    (re.compile(r"hermitian_?(?:form|bundle|space)", re.I), "HermitianSpace", r"\mathcal{V}", "Hermitian space"),
    (re.compile(r"orbital_?integral", re.I), "OrbitalIntegral", r"O_{\gamma}", "Orbital integral"),
    (re.compile(r"trace_?formula|rtf", re.I), "TraceFormula", r"\mathrm{Tr}", "Trace formula"),
    (re.compile(r"stepanov|auxiliary_?poly", re.I), "StepanovPoly", r"P_{\mathrm{aux}}", "Stepanov auxiliary polynomial"),
    (re.compile(r"adele_?ring|adelic", re.I), "AdeleRing", r"\mathbb{A}", "Adele ring"),
    (re.compile(r"tamagawa", re.I), "TamagawaMeasure", r"\tau", "Tamagawa measure"),
    (re.compile(r"mellin", re.I), "MellinTransform", r"\mathcal{M}", "Mellin transform"),
    (re.compile(r"fourier", re.I), "FourierTransform", r"\mathcal{F}", "Fourier transform"),
)

# Built-in Lean / Mathlib expression -> LaTeX translation table
_STANDARD_LEAN_TRANSLATIONS: tuple[tuple[re.Pattern[str], str], ...] = (
    # Common Mathlib / analytic number theory constants
    (re.compile(r"\bArithmeticFunction\.vonMangoldt\b|\bvonMangoldt\b"), r"\\Lambda"),
    (re.compile(r"\bDirichletCharacter\.LFunction\b"), r"L"),
    (re.compile(r"\bDirichletCharacter\b"), r"\\chi"),
    (re.compile(r"\bcompletedRiemannZeta\b"), r"\\Lambda"),
    (re.compile(r"\briemannZeta\b"), r"\\zeta"),
    (re.compile(r"\bRiemannHypothesis\b"), r"\\mathrm{RH}"),
    (
        re.compile(r"\bRiemannZetaZerosOnLine\b"),
        r"\\forall s \\in \\mathbb{C},\\; \\zeta(s) = 0 \\land 0 < \\operatorname{Re}(s) < 1 \\to \\operatorname{Re}(s) = 1 / 2",
    ),
    (
        re.compile(r"\bDirichletLZerosOnLine\b"),
        r"\\forall N \\ge 1,\\; \\forall \\chi \\pmod{N},\\; \\forall s \\in \\mathbb{C},\\; L(s, \\chi) = 0 \\land 0 < \\operatorname{Re}(s) < 1 \\to \\operatorname{Re}(s) = 1 / 2",
    ),
    (
        re.compile(r"\bPrimitiveDirichletLZerosOnLine\b"),
        r"\\forall N \\ge 1,\\; \\forall \\chi\\;\\mathrm{primitive} \\pmod{N},\\; \\forall s \\in \\mathbb{C},\\; L(s, \\chi) = 0 \\land 0 < \\operatorname{Re}(s) < 1 \\to \\operatorname{Re}(s) = 1 / 2",
    ),
    (
        re.compile(r"\bDirichletLNonvanishingRightOfHalf\b"),
        r"\\forall N \\ge 1,\\; \\forall \\chi \\pmod{N},\\; \\forall s \\in \\mathbb{C},\\; \\operatorname{Re}(s) > 1 / 2 \\to L(s, \\chi) \\neq 0",
    ),
    (re.compile(r"\bLFunction\b"), r"L"),
    (re.compile(r"\bNat\.Prime\b"), r"\\mathrm{Prime}"),
    (re.compile(r"\bPrime\b"), r"\\mathrm{Prime}"),
    # Measure theory / sums / products / limits / asymptotics
    (re.compile(r"\bMeasureTheory\.integral\b"), r"\\int"),
    (re.compile(r"\bFinset\.sum\b"), r"\\sum"),
    (re.compile(r"\bFinset\.prod\b"), r"\\prod"),
    (re.compile(r"\bFilter\.Tendsto\b"), r"\\to"),
    (re.compile(r"\bAsymptotics\.IsBigO\b"), r"O"),
    (re.compile(r"\bAsymptotics\.IsLittleO\b"), r"o"),
    # Classical groups & rings
    (re.compile(r"\bMatrix\.GeneralLinearGroup\b|\bGeneralLinearGroup\b"), r"\\mathrm{GL}"),
    (re.compile(r"\bMatrix\.SpecialLinearGroup\b|\bSpecialLinearGroup\b"), r"\\mathrm{SL}"),
    (re.compile(r"\bMatrix\.unitaryGroup\b|\bUnitaryGroup\b|\bunitaryGroup\b"), r"\\mathrm{U}"),
    (re.compile(r"\bSpecialUnitaryGroup\b"), r"\\mathrm{SU}"),
    (re.compile(r"\bSymplecticGroup\b"), r"\\mathrm{Sp}"),
    (re.compile(r"\bAdeleRing\b"), r"\\mathbb{A}"),
    (re.compile(r"\bPadicInt\b"), r"\\mathbb{Z}_p"),
    (re.compile(r"\bPadic\b"), r"\\mathbb{Q}_p"),
    (re.compile(r"\bZMod\b"), r"\\mathbb{Z}/\\mathbb{Z}"),
    # Number systems & elementary functions
    (re.compile(r"\bComplex\.re\b"), r"\\operatorname{Re}"),
    (re.compile(r"\bComplex\.im\b"), r"\\operatorname{Im}"),
    (re.compile(r"\bComplex\.abs\b"), r"\\mathrm{abs}"),
    (re.compile(r"\bComplex\.exp\b|\bReal\.exp\b"), r"\\exp"),
    (re.compile(r"\bComplex\.log\b|\bReal\.log\b"), r"\\log"),
    (re.compile(r"\bComplex\.I\b"), r"i"),
    (re.compile(r"\bReal\.pi\b"), r"\\pi"),
    (re.compile(r"\bComplex\.ofReal\b|\bNat\.cast\b|\bInt\.cast\b|\bRat\.cast\b"), r""),
    (re.compile(r"\bComplex\b"), r"\\mathbb{C}"),
    (re.compile(r"\bReal\b"), r"\\mathbb{R}"),
    (re.compile(r"\bRat\b"), r"\\mathbb{Q}"),
    (re.compile(r"\bInt\b"), r"\\mathbb{Z}"),
    (re.compile(r"\bNat\b"), r"\\mathbb{N}"),
    (re.compile(r"\bProp\b"), r"\\mathrm{Prop}"),
    (re.compile(r"\bType\s*\*?"), r"\\mathrm{Type}"),
    (re.compile(r"\bSet\b"), r"\\mathcal{P}"),
    (re.compile(r"\bFinset\b"), r"\\mathcal{F}"),
    (re.compile(r"\bMultiset\b"), r"\\mathcal{M}"),
    (re.compile(r"\bList\.map\b"), r"\\mathrm{map}"),
    (re.compile(r"\bList\.fold[lr]?\b"), r"\\mathrm{fold}"),
)

_UNICODE_TO_LATEX: tuple[tuple[str, str], ...] = (
    ("ℂ", r"\mathbb{C} "),
    ("ℝ", r"\mathbb{R} "),
    ("ℚ", r"\mathbb{Q} "),
    ("ℤ", r"\mathbb{Z} "),
    ("ℕ", r"\mathbb{N} "),
    ("∀", r"\forall "),
    ("∃", r"\exists "),
    ("→", r"\to "),
    ("↦", r"\mapsto "),
    ("↔", r"\iff "),
    ("∧", r"\land "),
    ("∨", r"\lor "),
    ("¬", r"\neg "),
    ("≤", r"\le "),
    ("≥", r"\ge "),
    ("≠", r"\neq "),
    ("∈", r"\in "),
    ("∉", r"\notin "),
    ("⊆", r"\subseteq "),
    ("⊂", r"\subset "),
    ("∪", r"\cup "),
    ("∩", r"\cap "),
    ("∅", r"\emptyset "),
    ("×", r"\times "),
    ("⊗", r"\otimes "),
    ("⊕", r"\oplus "),
    ("∘", r"\circ "),
    ("·", r"\cdot "),
    ("∑", r"\sum "),
    ("∏", r"\prod "),
    ("∫", r"\int "),
    ("∞", r"\infty "),
    ("π", r"\pi "),
    ("ζ", r"\zeta "),
    ("χ", r"\chi "),
    ("Λ", r"\Lambda "),
    ("λ", r"\lambda "),
    ("μ", r"\mu "),
    ("ν", r"\nu "),
    ("σ", r"\sigma "),
    ("τ", r"\tau "),
    ("θ", r"\theta "),
    ("Θ", r"\Theta "),
    ("φ", r"\varphi "),
    ("Φ", r"\Phi "),
    ("ψ", r"\psi "),
    ("Ψ", r"\Psi "),
    ("ω", r"\omega "),
    ("Ω", r"\Omega "),
    ("α", r"\alpha "),
    ("β", r"\beta "),
    ("γ", r"\gamma "),
    ("Γ", r"\Gamma "),
    ("δ", r"\delta "),
    ("Δ", r"\Delta "),
    ("ε", r"\varepsilon "),
    ("ρ", r"\rho "),
    ("‖", r"\| "),
    ("⟨", r"\langle "),
    ("⟩", r"\rangle "),
    ("⁻¹'", r"^{-1} "),
    ("⁻¹", r"^{-1} "),
    ("ᵒᵖ", r"^{\mathrm{op}} "),
    ("ˣ", r"^{\times} "),
    ("²", r"^2 "),
    ("³", r"^3 "),
    ("†", r"^{\dagger} "),
    ("ᴴ", r"^{\mathrm{H}} "),
    ("ᵀ", r"^{\mathrm{T}} "),
    ("ᵁ", r"^{\mathrm{U}} "),
    ("ᵐ", r"^{m} "),
    ("ᵒ", r"^{o} "),
    ("ᵖ", r"^{p} "),
    ("ᶠ", r"^{f} "),
    ("⁻", r"^{-} "),
    ("₀", r"_0 "),
    ("₁", r"_1 "),
    ("₂", r"_2 "),
    ("₃", r"_3 "),
    ("₄", r"_4 "),
    ("₅", r"_5 "),
    ("₆", r"_6 "),
    ("₇", r"_7 "),
    ("₈", r"_8 "),
    ("₉", r"_9 "),
    ("ₐ", r"_{a} "),
    ("ₑ", r"_{e} "),
    ("ₕ", r"_{h} "),
    ("ᵢ", r"_{i} "),
    ("ⱼ", r"_{j} "),
    ("ₖ", r"_{k} "),
    ("ₗ", r"_{l} "),
    ("ₘ", r"_{m} "),
    ("ₙ", r"_{n} "),
    ("ₒ", r"_{o} "),
    ("ₚ", r"_{p} "),
    ("ᵣ", r"_{r} "),
    ("ₛ", r"_{s} "),
    ("ₜ", r"_{t} "),
    ("ᵤ", r"_{u} "),
    ("ᵥ", r"_{v} "),
    ("ₓ", r"_{x} "),
    ("Σ", r"\Sigma "),
    ("η", r"\eta "),
    ("ι", r"\iota "),
    ("ξ", r"\xi "),
    ("κ", r"\kappa "),
    ("≃", r"\simeq "),
    ("≅", r"\cong "),
    ("≈", r"\approx "),
    ("∼", r"\sim "),
    ("±", r"\pm "),
    ("⊢", r"\vdash "),
    ("•", r"\cdot "),
    ("⬝", r"\cdot "),
    ("∗", r"\ast "),
    ("⋆", r"\star "),
    ("ℓ", r"\ell "),
    ("⧸", r"/"),
    ("↥", ""),
    ("↓", ""),
    ("∂", r"\partial "),
    ("≫", r"\gg "),
    ("≪", r"\ll "),
    ("⊓", r"\sqcap "),
    ("⊔", r"\sqcup "),
    ("⊤", r"\top "),
    ("⊥", r"\bot "),
    ("⟦", r"[\![ "),
    ("⟧", r"]\!] "),
    ("⟶", r"\longrightarrow "),
    ("⟵", r"\longleftarrow "),
    ("⥤", r"\Rightarrow "),
    ("𝓝", r"\mathcal{N} "),
    ("𝓞", r"\mathcal{O} "),
    ("𝟙", r"\mathbf{1} "),
)

# Glue binders / clauses to strip from Lean types before exposing math
_GLUE_HYPOTHESIS_RE = re.compile(
    r"\b(Decidable(?:Eq|Pred|Rel)?|Measurable(?:Space)?|AEMeasurable|"
    r"StronglyMeasurable|Fintype|Finite|Inhabited|Nonempty|NeZero|"
    r"Subsingleton|Nontrivial|TopologicalSpace|NormedAddCommGroup|"
    r"NormedSpace|InnerProductSpace|Module|Algebra|CommRing|Field|"
    r"AddCommGroup|Group|Monoid|LinearOrder|PartialOrder|Preorder)\b"
)


@dataclass(slots=True)
class SymbolEntry:
    """Single entry in the global symbol registry."""

    decl_id: int
    lean_name: str
    short_name: str
    module_path: str
    kind: str
    latex_macro: str
    display_name: str
    math_definition: str
    centrality: float

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class SymbolRegistry:
    """In-memory view of the global symbol registry."""

    entries: list[SymbolEntry] = field(default_factory=list)
    by_lean_name: dict[str, SymbolEntry] = field(default_factory=dict)
    by_short_name: dict[str, SymbolEntry] = field(default_factory=dict)
    by_macro: dict[str, SymbolEntry] = field(default_factory=dict)

    def add(self, entry: SymbolEntry) -> None:
        self.entries.append(entry)
        self.by_lean_name[entry.lean_name] = entry
        if entry.short_name not in self.by_short_name:
            self.by_short_name[entry.short_name] = entry
        self.by_macro[entry.latex_macro] = entry

    def macros_set(self) -> set[str]:
        return set(self.by_macro.keys())

    def render_preamble(self) -> str:
        """Emit LaTeX \\providecommand lines for every registered macro."""
        lines = ["% --- Global Symbol Registry Macros (anchored to Lean declarations) ---"]
        for entry in self.entries:
            macro = entry.latex_macro
            defn = entry.math_definition
            lines.append(
                f"\\providecommand{{{macro}}}{{{defn}}} % {entry.lean_name}"
            )
        return "\n".join(lines)

    @classmethod
    def load_from_db(cls, db: DbHandle) -> "SymbolRegistry":
        reg = cls()
        with open_db(db, readonly=False) as conn:
            rows = query_all(
                conn,
                """
                SELECT s.decl_id, s.latex_macro, s.display_name, s.math_definition, s.centrality,
                       d.name AS lean_name, d.short_name, d.kind,
                       COALESCE(mod.path, '') AS module_path
                FROM symbols s
                JOIN declarations d ON d.id = s.decl_id
                LEFT JOIN modules mod ON mod.id = d.module_id
                ORDER BY s.centrality DESC, s.decl_id ASC
                """,
            )
        for r in rows:
            reg.add(
                SymbolEntry(
                    decl_id=int(r["decl_id"]),
                    lean_name=str(r["lean_name"]),
                    short_name=str(r["short_name"] or r["lean_name"].rsplit(".", 1)[-1]),
                    module_path=str(r["module_path"] or ""),
                    kind=str(r["kind"] or "def"),
                    latex_macro=str(r["latex_macro"]),
                    display_name=str(r["display_name"]),
                    math_definition=str(r["math_definition"]),
                    centrality=float(r["centrality"] or 0.0),
                )
            )
        return reg


def _to_alpha_camel(name: str) -> str:
    """Convert an arbitrary Lean identifier into a pure ASCII-letter CamelCase token."""
    short = name.rsplit(".", 1)[-1]
    parts = re.split(r"[^A-Za-z]+", short)
    cleaned = "".join(p[:1].upper() + p[1:] for p in parts if p)
    if not cleaned:
        cleaned = "Sym"
    if len(cleaned) > 24:
        cleaned = cleaned[:24]
    return cleaned


def _humanize_name(name: str) -> str:
    """Convert Lean snake_case / CamelCase identifier to clean readable words."""
    short = name.rsplit(".", 1)[-1]
    spaced = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", short)
    spaced = spaced.replace("_", " ").strip()
    return spaced or short


def _assign_macro_and_math(
    lean_name: str,
    short_name: str,
    used_macros: set[str],
) -> tuple[str, str, str]:
    """Choose a unique, valid LaTeX macro, its rendered math form, and display name."""
    camel_norm = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", lean_name)

    base_macro: str | None = None
    math_def: str | None = None
    display_name = _humanize_name(short_name)

    for pat, m_base, m_tex, disp in _DOMAIN_NOTATION_RULES:
        if pat.search(camel_norm):
            base_macro = m_base
            math_def = m_tex
            if len(display_name) <= 3:
                display_name = disp
            break

    if base_macro is None:
        base_macro = "pc" + _to_alpha_camel(short_name)
    if math_def is None:
        # Clean operator name without underscores/digits leaking raw Lean syntax
        label = _to_alpha_camel(short_name)
        if len(label) > 12:
            label = label[:12]
        math_def = rf"\operatorname{{{label}}}"

    # Guarantee strictly alphabetic TeX command name with no collisions
    candidate = base_macro
    if candidate in _RESERVED_LATEX_MACROS:
        candidate = "pc" + candidate

    suffix_idx = 0
    alpha_suffixes = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    final_name = candidate
    while f"\\{final_name}" in used_macros or final_name in _RESERVED_LATEX_MACROS:
        if suffix_idx < len(alpha_suffixes):
            final_name = f"{candidate}{alpha_suffixes[suffix_idx]}"
        else:
            q, r = divmod(suffix_idx, len(alpha_suffixes))
            final_name = f"{candidate}{alpha_suffixes[q % 26]}{alpha_suffixes[r]}"
        suffix_idx += 1

    macro = f"\\{final_name}"
    used_macros.add(macro)
    return macro, math_def, display_name


def build_symbol_registry(
    db: DbHandle,
    *,
    max_symbols: int = 120,
    reachable_only: bool = True,
) -> SymbolRegistry:
    """Populate the `symbols` table from high-centrality non-Mathlib definitions."""
    registry = SymbolRegistry()
    with open_db(db, readonly=False) as conn:
        use_reach = reachable_only and has_reachable_metrics(conn)
        placeholders = ",".join("?" for _ in SYMBOL_DECL_KINDS)

        if use_reach:
            rows = query_all(
                conn,
                f"""
                SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.docstring,
                       d.body_loc, COALESCE(mod.path, '') AS module_path,
                       COALESCE(m.in_degree, 0) AS in_degree,
                       COALESCE(m.out_degree, 0) AS out_degree,
                       COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score
                FROM declarations d
                JOIN metrics m ON m.decl_id = d.id
                LEFT JOIN modules mod ON mod.id = d.module_id
                WHERE m.reachable = 1
                  AND d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                  AND d.kind IN ({placeholders})
                ORDER BY CASE WHEN LENGTH(COALESCE(d.short_name, '')) >= 3 THEN 1 ELSE 0 END DESC,
                         CASE WHEN TRIM(LTRIM(COALESCE(d.type_sig, ''), ':')) IN ('Prop', '') THEN 0 ELSE 1 END DESC,
                         (COALESCE(m.in_degree, 0) * 2.0 + COALESCE(m.bottleneck_score, 0.0) + MIN(d.body_loc, 100) * 0.1) DESC,
                         d.id ASC
                LIMIT ?
                """,
                (*SYMBOL_DECL_KINDS, max_symbols),
            )
        else:
            rows = query_all(
                conn,
                f"""
                SELECT d.id, d.name, d.short_name, d.kind, d.type_sig, d.docstring,
                       d.body_loc, COALESCE(mod.path, '') AS module_path,
                       (SELECT COUNT(*) FROM edges e WHERE e.dst_id = d.id) AS in_degree,
                       (SELECT COUNT(*) FROM edges e WHERE e.src_id = d.id) AS out_degree,
                       0.0 AS bottleneck_score
                FROM declarations d
                LEFT JOIN modules mod ON mod.id = d.module_id
                WHERE d.is_mathlib = 0
                  AND d.is_bookkeeping = 0
                  AND d.kind IN ({placeholders})
                ORDER BY in_degree DESC, d.body_loc DESC, d.id ASC
                LIMIT ?
                """,
                (*SYMBOL_DECL_KINDS, max_symbols),
            )

        used_macros: set[str] = set()
        insert_rows: list[tuple[int, str, str, str, float]] = []

        for r in rows:
            lean_name = str(r["name"])
            short_name = str(r["short_name"] or lean_name.rsplit(".", 1)[-1])
            in_deg = float(r["in_degree"] or 0.0)
            bn = float(r["bottleneck_score"] or 0.0)
            body_loc = float(r["body_loc"] or 0.0)
            centrality = round(in_deg * 2.0 + bn + min(body_loc, 100.0) * 0.1, 4)

            macro, math_def, display_name = _assign_macro_and_math(
                lean_name, short_name, used_macros
            )

            entry = SymbolEntry(
                decl_id=int(r["id"]),
                lean_name=lean_name,
                short_name=short_name,
                module_path=str(r["module_path"] or ""),
                kind=str(r["kind"] or "def"),
                latex_macro=macro,
                display_name=display_name,
                math_definition=math_def,
                centrality=centrality,
            )
            registry.add(entry)
            insert_rows.append(
                (entry.decl_id, entry.latex_macro, entry.display_name, entry.math_definition, entry.centrality)
            )

        conn.execute("DELETE FROM symbols")
        if insert_rows:
            conn.executemany(
                """
                INSERT INTO symbols (decl_id, latex_macro, display_name, math_definition, centrality)
                VALUES (?, ?, ?, ?, ?)
                """,
                insert_rows,
            )
        conn.commit()

    return registry


def _strip_balanced_blocks(text: str, open_ch: str, close_ch: str) -> str:
    """Remove top-level balanced binder blocks like `[...]` or `{...}` from Lean signatures."""
    out: list[str] = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == open_ch:
            depth += 1
            if depth == 1:
                out.append(" ")
        elif ch == close_ch and depth > 0:
            depth -= 1
        elif depth == 0:
            out.append(ch)
        i += 1
    return "".join(out)


def _strip_glue_parenthesized_binders(text: str) -> str:
    """Drop explicit hypothesis binders like `(h : Measurable f)` or `(h : Decidable P)`."""
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text[i] == "(":
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                if text[j] == "(":
                    depth += 1
                elif text[j] == ")":
                    depth -= 1
                j += 1
            block = text[i:j]
            if ":" in block and _GLUE_HYPOTHESIS_RE.search(block):
                # Drop routine typeclass/measurability hypothesis binder
                out.append(" ")
                i = j
                continue
        out.append(text[i])
        i += 1
    return "".join(out)


def escape_latex_text(text: str) -> str:
    """Escape plain prose text safely for LaTeX (outside math mode)."""
    if not text:
        return ""
    import unicodedata

    # Normalize any non-ASCII chars in prose/titles to ASCII equivalents
    normalized = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode("ascii")
    replacements = (
        ("\\", r"\textbackslash{}"),
        ("&", r"\&"),
        ("%", r"\%"),
        ("$", r"\$"),
        ("#", r"\#"),
        ("_", r"\_"),
        ("{", r"\{"),
        ("}", r"\}"),
        ("~", r"\textasciitilde{}"),
        ("^", r"\textasciicircum{}"),
    )
    out = normalized
    for old, new in replacements:
        out = out.replace(old, new)
    return out


def lean_type_to_latex(
    type_sig: str,
    registry: SymbolRegistry | None = None,
    *,
    max_len: int = 500,
) -> str:
    """Translate a Lean 4 type signature into clean, readable LaTeX math notation."""
    if not type_sig or not type_sig.strip():
        return r"\text{(type signature omitted)}"

    s = " ".join(type_sig.split())
    # Drop leading `:` if captured by parser
    if s.startswith(":"):
        s = s[1:].strip()

    # Strip Lean instance `[...]` and implicit `{...}` / `⦃...⦄` binders
    s = _strip_balanced_blocks(s, "[", "]")
    s = _strip_balanced_blocks(s, "{", "}")
    s = _strip_balanced_blocks(s, "⦃", "⦄")
    s = _strip_glue_parenthesized_binders(s)

    # Strip Lean coercion arrow `↑` and escape TeX-hostile characters from Lean syntax
    s = s.replace("↑", "")
    s = s.replace(" \\ ", " SETMINUS_TOK ")
    s = s.replace("\\", "")
    s = s.replace("&&", r" \land ")
    s = s.replace("||", r" \lor ")
    s = s.replace("%", r" \bmod ")
    s = s.replace("&", r"\&")
    s = s.replace("#", r"\#")
    s = s.replace("$", r" ")
    s = s.replace("SETMINUS_TOK", r"\setminus ")
    s = re.sub(r"\s+", " ", s).strip()

    # Truncate extraordinarily long signatures gracefully before tokenizing
    truncated = False
    if len(s) > max_len:
        s = s[:max_len].rsplit(" ", 1)[0]
        truncated = True

    # Replace registered Lean constants (longest first so qualified names win)
    if registry and registry.entries:
        # Sort by full lean_name length descending
        for entry in sorted(
            registry.entries, key=lambda e: len(e.lean_name), reverse=True
        ):
            if entry.lean_name in s:
                s = re.sub(
                    rf"(?<![A-Za-z0-9_.]){re.escape(entry.lean_name)}(?![A-Za-z0-9_])",
                    lambda _m, mac=entry.latex_macro: mac + " ",
                    s,
                )
        for entry in sorted(
            registry.entries, key=lambda e: len(e.short_name), reverse=True
        ):
            if len(entry.short_name) >= 4 and entry.short_name in s:
                s = re.sub(
                    rf"(?<![A-Za-z0-9_\\]){re.escape(entry.short_name)}(?![A-Za-z0-9_])",
                    lambda _m, mac=entry.latex_macro: mac + " ",
                    s,
                )

    # Standard Lean / Mathlib expression translations
    for pat, repl in _STANDARD_LEAN_TRANSLATIONS:
        s = pat.sub(repl, s)

    # ASCII arrow / logic operators
    s = s.replace("<->", r"\iff ")
    s = s.replace("->", r"\to ")
    s = s.replace("=>", r"\mapsto ")
    s = s.replace("<=", r"\le ")
    s = s.replace(">=", r"\ge ")
    s = s.replace("!=", r"\neq ")
    s = re.sub(r"(?<!\\)\bforall\b", r"\\forall ", s)
    s = re.sub(r"(?<!\\)\bexists\b", r"\\exists ", s)
    s = re.sub(r"(?<!\\)\bfun\b", r"\\lambda ", s)

    # Unicode symbols -> LaTeX
    for uni, tex in _UNICODE_TO_LATEX:
        if uni in s:
            s = s.replace(uni, tex)

    # Clean up remaining dotted / snake_case Lean identifiers so TeX math mode never chokes on `_`
    def _clean_ident(m: re.Match[str]) -> str:
        tok = m.group(0).strip(".")
        if not tok:
            return ""
        if tok.startswith("\\"):
            return tok
        parts = [p for p in tok.split(".") if p]
        if not parts:
            return ""
        if len(parts) == 2 and len(parts[0]) <= 3 and "_" not in parts[0]:
            # Short variable field projection like `j.val` or `s.re`
            tail_safe = parts[1].replace("_", r"\_")
            return rf"{parts[0]}.\mathrm{{{tail_safe}}}"
        tail = parts[-1].replace("_", r"\_")
        return rf"\mathrm{{{tail}}}"

    s = re.sub(
        r"(?<!\\)\b[A-Za-z][A-Za-z0-9_.]*(?:_[A-Za-z0-9_.]*|\.[A-Za-z0-9_.]*)+\b\.?",
        _clean_ident,
        s,
    )
    # Also wrap standalone multi-letter CamelCase identifiers (>= 3 letters, not TeX commands) in \mathrm{...}
    s = re.sub(
        r"(?<![\\{A-Za-z0-9_])\b([A-Za-z][A-Za-z0-9]{2,})\b(?!\})",
        r"\\mathrm{\1}",
        s,
    )
    # Remove any stray standalone underscores not escaped
    s = re.sub(r"(?<!\\)_(?![{A-Za-z0-9])", r"\_", s)

    # Normalize any remaining non-ASCII characters to ASCII so TeX fonts never miss glyphs
    import unicodedata

    if any(ord(ch) > 127 for ch in s):
        s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii")

    # Prevent TeX double superscripts (`^{...}'`, `^a'`, `^a ^b`) and double subscripts (`_a _b`)
    s = re.sub(r"(\^\{[^}]*\}|\^[A-Za-z0-9])\s*'+", r"\1", s)
    s = re.sub(r"'+(\s*\^)", r"\1", s)
    while re.search(r"(\^\{[^}]*\}|\^\\[A-Za-z]+|\^[A-Za-z0-9])\s*\^", s):
        s = re.sub(r"(\^\{[^}]*\}|\^\\[A-Za-z]+|\^[A-Za-z0-9])\s*\^", r"\1 \\cdot ", s)
    while re.search(r"(_\{[^}]*\}|_\\[A-Za-z]+|_[A-Za-z0-9])\s*_", s):
        s = re.sub(r"(_\{[^}]*\}|_\\[A-Za-z]+|_[A-Za-z0-9])\s*_", r"\1 ", s)

    # Balance parentheses defensively
    open_p = s.count("(")
    close_p = s.count(")")
    if open_p > close_p:
        s = s + ")" * (open_p - close_p)
    elif close_p > open_p:
        s = "(" * (close_p - open_p) + s

    # Balance curly braces defensively
    open_b = s.count("{") - s.count(r"\{")
    close_b = s.count("}") - s.count(r"\}")
    if open_b > close_b:
        s = s + "}" * (open_b - close_b)
    elif close_b > open_b:
        # Remove extra unmatched closing braces from the right
        diff = close_b - open_b
        while diff > 0 and "}" in s:
            idx = s.rfind("}")
            if idx > 0 and s[idx - 1] == "\\":
                break
            s = s[:idx] + s[idx + 1 :]
            diff -= 1

    s = re.sub(r"\s+", " ", s).strip()
    if truncated:
        s += r" \;\cdots"
    return s or r"\text{(statement)}"
