"""Fast Lean 4 source parser for declarations, canonical type hashes, and references."""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from typing import Iterable

# ---------------------------------------------------------------------------
# Package / Mathlib detection
# ---------------------------------------------------------------------------

MATHLIB_ROOT_PACKAGES = frozenset({
    "Mathlib",
    "Std",
    "Init",
    "Batteries",
    "Qq",
    "Aesop",
    "Lean",
    "ProofWidgets",
    "ImportGraph",
    "Plausible",
    "Lake",
})

STRIP_LEADING_DIRS = frozenset({".", "lean", "src", "Lean"})

# ---------------------------------------------------------------------------
# Comment / docstring scanner
# ---------------------------------------------------------------------------

_COMMENT_TOKEN_RE = re.compile(
    r'/--'
    r'|/-'
    r'|-/'
    r'|--[^\n]*'
    r'|"(?:\\.|[^"\\])*"'
)

# ---------------------------------------------------------------------------
# Top-level command & declaration patterns
# ---------------------------------------------------------------------------

_IMPORT_RE = re.compile(
    r"^(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.\u0080-\uffff]+)"
)
_NAMESPACE_RE = re.compile(
    r"^namespace\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*)"
)
_SECTION_RE = re.compile(
    r"^(?:noncomputable\s+)?section(?:\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*))?\b"
)
_END_RE = re.compile(
    r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.\u0080-\uffff']*))?\s*$"
)
_OPEN_RE = re.compile(r"^open\s+(.*)")
_MUTUAL_RE = re.compile(r"^mutual\s*$")

_MODIFIER_PREFIX = (
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|public|noncomputable|partial|unsafe|meta|scoped|local)\s+)*"
)

_DECL_KW_GROUP = (
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque|constant)"
)

_DECL_START_RE = re.compile(
    r"^" + _MODIFIER_PREFIX + _DECL_KW_GROUP + r"\b(.*)$"
)

_OPEN_IN_DECL_RE = re.compile(
    r"^open\s+(.*?)\s+in\s+(" + _MODIFIER_PREFIX + _DECL_KW_GROUP + r"\b.*)$"
)

_ATTR_ONLY_RE = re.compile(r"^@\[[^\]]*\]\s*$")
_ATTR_START_RE = re.compile(r"^@\[")
_MODIFIER_ONLY_RE = re.compile(
    r"^(?:(?:private|protected|public|noncomputable|partial|unsafe|meta|scoped|local)\s*)+$"
)

# Commands that terminate a previous declaration at column 0
_TOP_COMMAND_RE = re.compile(
    r"^(?:"
    r"import|public\s+import|private\s+import|meta\s+import|"
    r"namespace|section|noncomputable\s+section|end|open|export|"
    r"variable|variables|universe|universes|attribute|local\s+attribute|scoped\s+attribute|"
    r"set_option|notation|local\s+notation|scoped\s+notation|"
    r"macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat|"
    r"infix|infixl|infixr|prefix|postfix|local\s+infix|scoped\s+infix|"
    r"example|mutual|initialize|builtin_initialize|deriving\s+instance|"
    r"add_decl_doc|run_cmd|register_simp_attr|suppress_compilation|"
    r"#check|#print|#eval|#reduce|#synth|#guard|#align|#check_failure"
    r")\b"
)

_IDENT_NAME_RE = re.compile(
    r"^(?:«([^»]+)»|([A-Za-z_][A-Za-z0-9_'\u0080-\uffff]*(?:\.[A-Za-z_][A-Za-z0-9_'\u0080-\uffff]*)*))"
)

# Identifier extraction for references
_REF_IDENT_RE = re.compile(
    r"(?<![A-Za-z0-9_'\.])"
    r"([A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*(?:\.[A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*)*)"
)

# ---------------------------------------------------------------------------
# Lean 4 keywords, tactics, and noise tokens excluded from reference extraction
# ---------------------------------------------------------------------------

LEAN_STOPWORDS = frozenset({
    # Core language keywords
    "theorem", "lemma", "def", "abbrev", "structure", "class", "inductive",
    "instance", "axiom", "opaque", "constant", "example", "where", "extends",
    "deriving", "namespace", "section", "end", "open", "scoped", "hiding",
    "renaming", "import", "export", "variable", "variables", "universe",
    "universes", "private", "protected", "public", "noncomputable", "partial",
    "unsafe", "meta", "local", "mutual", "attribute", "set_option",
    "by", "have", "let", "letI", "haveI", "show", "from", "fun", "match",
    "with", "if", "then", "else", "do", "return", "for", "in", "unless",
    "try", "catch", "finally", "calc", "suffices", "nomatch", "nofun",
    "sorry", "admit", "Type", "Prop", "Sort", "true", "false", "and", "or",
    "not", "forall", "exists", "fun", "at", "only", "using", "as", "is",
    "to", "of", "on", "this", "it",
    # Common tactics
    "simp", "dsimp", "simp_all", "simpa", "simp_rw", "rw", "rwa", "erw",
    "exact", "apply", "refine", "intro", "intros", "rintro", "rcases",
    "obtain", "cases", "induction", "rcases", "constructor", "left", "right",
    "use", "existsi", "specialize", "generalize", "clear", "revert", "subst",
    "change", "conv", "conv_lhs", "conv_rhs", "ring", "ring_nf", "linarith",
    "nlinarith", "omega", "norm_num", "norm_cast", "push_cast", "positivity",
    "field_simp", "aesop", "tauto", "decide", "rfl", "trivial", "contradiction",
    "exfalso", "by_contra", "by_cases", "split", "split_ifs", "ext", "funext",
    "congr", "congr_arg", "gcongr", "mono", "bound", "continuity",
    "measurability", "fun_prop", "abel", "group", "module", "polyrith",
    "linear_combination", "trans", "symm", "calc", "nth_rw", "set", "rename_i",
    "all_goals", "any_goals", "first", "repeat", "try", "done", "swap",
    "rotate_left", "rotate_right", "assumption", "filter_upwards", "fin_cases",
    "interval_cases", "decide", "native_decide", "ac_rfl", "pi_instance",
    "infer_instance", "exact_mod_cast", "apply_mod_cast", "rw_mod_cast",
    "push_neg", "contrapose", "choose", "classical", "wlog", "peel", "rel",
    "grw", "grind", "lia",
    # Very generic single/two-letter proof names
    "h", "h1", "h2", "h3", "h4", "h5", "h0", "hx", "hy", "hz", "hs", "ht",
    "hn", "hm", "hk", "hi", "hj", "hp", "hq", "hr", "ha", "hb", "hc", "hd",
    "he", "hf", "hg", "h'", "ih", "IH", "eq", "ne", "lt", "le", "gt", "ge",
    "mp", "mpr", "fst", "snd", "val", "prop", "mk", "rec", "casesOn",
    "zero", "one", "add", "sub", "mul", "div", "neg", "inv", "pow", "mod",
    "map", "bind", "pure", "get", "set", "len", "size", "length",
})

# ---------------------------------------------------------------------------
# Bookkeeping heuristics
# ---------------------------------------------------------------------------

_BOOKKEEPING_NAME_RE = re.compile(
    r"(?:^|_)(?:"
    r"coe|cast|decidable|measurable|aemeasurable|aestronglymeasurable|"
    r"stronglymeasurable|integrable|continuous|differentiable|"
    r"nonempty|inhabited|subsingleton|fintype|countable|finite|"
    r"ext_iff|mk_iff|ofNat|aux|helper|simp_aux|inst"
    r")(?:$|_|\d)",
    re.IGNORECASE,
)

_BOOKKEEPING_RET_TYPE_RE = re.compile(
    r"^\s*(?:"
    r"Decidable|DecidableEq|DecidablePred|DecidableRel|"
    r"Measurable|AEMeasurable|AEStronglyMeasurable|StronglyMeasurable|"
    r"Integrable|LocallyIntegrable|Continuous|ContinuousOn|ContinuousAt|"
    r"Differentiable|DifferentiableOn|DifferentiableAt|"
    r"Finite|Fintype|Nonempty|Inhabited|Subsingleton|Countable|"
    r"NeZero|IsEmpty|Unique|Nontrivial"
    r")\b"
)

_TRIVIAL_BODY_RE = re.compile(
    r"^\s*(?::=\s*)?(?:by\s+)?(?:"
    r"rfl|trivial|decide|tauto|aesop|simp(?:\s*\[[^\]]*\])?|"
    r"norm_num|ring|ring_nf|linarith|omega|positivity|"
    r"measurability|continuity|fun_prop|infer_instance|push_cast"
    r")\s*$"
)

# ---------------------------------------------------------------------------
# Canonical type hashing (alpha-equivalence modulo binder names & whitespace)
# ---------------------------------------------------------------------------

_UNICODE_NORM = (
    ("<->", "↔"),
    ("->", "→"),
    ("<-", "←"),
    ("=>", "⇒"),
)

_BINDER_GROUP_RE = re.compile(
    r"([(\[{⦃])\s*"
    r"([A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*(?:\s+[A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*)*)"
    r"\s*:"
)

_QUANT_BINDER_RE = re.compile(
    r"(∀|∃|λ)\s*"
    r"([A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*(?:\s+[A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*)*)"
    r"(?=\s*(?::|,|⇒))"
)

_STANDALONE_IDENT_RE = re.compile(
    r"(?<![A-Za-z0-9_'\.])([A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*)(?![A-Za-z0-9_'])"
)

_PUNCT_SPACE_RE = re.compile(r"\s*([()\[\]{}⦃⦄:,.→←↔∀∃λ⇒])\s*")


_BINDER_KEYWORDS = frozenset({
    "forall", "exists", "fun", "let", "have", "if", "then", "else",
    "match", "with", "do", "in", "by", "where", "Prop", "Type", "Sort", "_",
})


def _extract_binder_names(type_sig: str) -> list[str]:
    """Return bound variable names in order of first appearance in type_sig."""
    seen: set[str] = set()
    ordered: list[str] = []

    def _add(names_str: str) -> None:
        for tok in names_str.split():
            if tok not in _BINDER_KEYWORDS and tok not in seen:
                seen.add(tok)
                ordered.append(tok)

    # Collect matches ordered by position
    hits: list[tuple[int, str]] = []
    for m in _BINDER_GROUP_RE.finditer(type_sig):
        bracket = m.group(1)
        names_str = m.group(2)
        # In instance binders `[Foo α]`, there is no `:`; if `[inst : Foo α]`, `inst` is a binder name.
        if bracket in ("(", "{", "[", "⦃"):
            hits.append((m.start(), names_str))
    for m in _QUANT_BINDER_RE.finditer(type_sig):
        hits.append((m.start(), m.group(2)))

    hits.sort(key=lambda x: x[0])
    for _, names_str in hits:
        _add(names_str)
    return ordered


def canonicalize_type(type_sig: str) -> str:
    """Normalize a Lean 4 type signature modulo binder names, Unicode aliases, and whitespace."""
    if not type_sig:
        return ""
    s = type_sig
    # Word-level keyword normalization
    s = re.sub(r"\bforall\b", "∀", s)
    s = re.sub(r"\bexists\b", "∃", s)
    s = re.sub(r"\bfun\b", "λ", s)
    for ascii_op, uni_op in _UNICODE_NORM:
        s = s.replace(ascii_op, uni_op)
    s = " ".join(s.split())

    binders = _extract_binder_names(s)
    if binders:
        mapping = {name: f"_v{idx}" for idx, name in enumerate(binders)}
        s = _STANDALONE_IDENT_RE.sub(
            lambda m: mapping.get(m.group(1), m.group(1)),
            s,
        )

    # Normalize spacing around punctuation/operators
    s = _PUNCT_SPACE_RE.sub(r"\1", s)
    return s.strip()


def canonical_type_hash(type_sig: str) -> str:
    """Return a stable 24-hex-char SHA-256 hash of the canonicalized type signature."""
    canon = canonicalize_type(type_sig)
    if not canon:
        return ""
    return hashlib.sha256(canon.encode("utf-8")).hexdigest()[:24]


# ---------------------------------------------------------------------------
# Data models
# ---------------------------------------------------------------------------


@dataclass
class ParsedDecl:
    name: str
    short_name: str
    kind: str
    type_sig: str
    canonical_type_hash: str
    body_loc: int
    docstring: str | None
    is_bookkeeping: bool
    start_line: int
    end_line: int
    is_private: bool = False
    namespace_stack: tuple[str, ...] = ()
    open_namespaces: tuple[str, ...] = ()
    type_refs: list[str] = field(default_factory=list)
    proof_refs: list[str] = field(default_factory=list)


@dataclass
class ParsedModule:
    path: str
    package: str
    loc: int
    is_mathlib: bool
    imports: list[str] = field(default_factory=list)
    declarations: list[ParsedDecl] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Path normalization
# ---------------------------------------------------------------------------


def normalize_module_path(
    raw_path: str,
    *,
    strip_prefixes: Iterable[str] = (),
) -> tuple[str, str, bool]:
    """Normalize a file path (from tar archive or filesystem) into (module_path, package, is_mathlib).

    Examples:
      'lean/RH/Core/Zeta.lean' -> ('RH.Core.Zeta', 'RH', False)
      './.lake/packages/mathlib/Mathlib/Data/Nat/Basic.lean' -> ('Mathlib.Data.Nat.Basic', 'Mathlib', True)
      'Main.lean' -> ('Main', 'Main', False)
    """
    p = raw_path.replace("\\", "/").lstrip("/")
    while p.startswith("./"):
        p = p[2:]

    is_lake_pkg = False
    for marker in (".lake/packages/", "lake-packages/"):
        idx = p.find(marker)
        if idx != -1:
            is_lake_pkg = True
            rest = p[idx + len(marker):]
            parts = rest.split("/", 1)
            if len(parts) == 2:
                # e.g. mathlib/Mathlib/Algebra/... -> Mathlib/Algebra/...
                p = parts[1]
            break

    for pref in strip_prefixes:
        pref_clean = pref.strip("/") + "/"
        if p.startswith(pref_clean):
            p = p[len(pref_clean):]
            break

    parts = [seg for seg in p.split("/") if seg]
    while len(parts) > 1 and parts[0] in STRIP_LEADING_DIRS:
        parts = parts[1:]

    if parts and parts[-1].endswith(".lean"):
        parts[-1] = parts[-1][:-5]

    mod_path = ".".join(parts) if parts else raw_path
    package = parts[0] if parts else ""
    is_mathlib = is_lake_pkg or (package in MATHLIB_ROOT_PACKAGES)
    return mod_path, package, is_mathlib


# ---------------------------------------------------------------------------
# Comment stripping & docstring extraction
# ---------------------------------------------------------------------------


def strip_comments_and_extract_docstrings(source: str) -> tuple[str, dict[int, str]]:
    """Replace Lean 4 comments with spaces (preserving newlines) and return docstrings by end_line (1-based)."""
    if "--" not in source and "/-" not in source:
        return source, {}

    out_parts: list[str] = []
    docstrings: dict[int, str] = {}
    last_pos = 0
    depth = 0
    block_start = 0
    is_doc = False

    # Precompute newline count incrementally for fast end_line tracking
    # (Avoids O(N^2) source.count('\n', 0, pos) on large files!)
    line_num = 1
    counted_up_to = 0

    def _line_at(pos: int) -> int:
        nonlocal line_num, counted_up_to
        if pos > counted_up_to:
            line_num += source.count("\n", counted_up_to, pos)
            counted_up_to = pos
        return line_num

    for m in _COMMENT_TOKEN_RE.finditer(source):
        tok = m.group(0)
        start, end = m.start(), m.end()

        if depth == 0:
            if tok[0] == '"':
                # String literal — keep untouched
                continue
            if tok.startswith("--"):
                out_parts.append(source[last_pos:start])
                out_parts.append(" " * (end - start))
                last_pos = end
            elif tok == "/--":
                out_parts.append(source[last_pos:start])
                depth = 1
                block_start = start
                is_doc = True
            elif tok == "/-":
                out_parts.append(source[last_pos:start])
                depth = 1
                block_start = start
                is_doc = False
            # Stray '-/' at depth 0: ignore
        else:
            if tok == "/-" or tok == "/--":
                depth += 1
            elif tok == "-/":
                depth -= 1
                if depth == 0:
                    span = source[block_start:end]
                    if is_doc:
                        raw_doc = span[3:-2].strip()
                        docstrings[_line_at(end)] = raw_doc
                    # Replace block comment with newlines only (preserving exact line count)
                    nl_count = span.count("\n")
                    out_parts.append("\n" * nl_count if nl_count else " ")
                    last_pos = end

    if depth > 0:
        # Unclosed block comment at EOF
        span = source[block_start:]
        nl_count = span.count("\n")
        out_parts.append("\n" * nl_count if nl_count else " ")
    else:
        out_parts.append(source[last_pos:])

    return "".join(out_parts), docstrings


# ---------------------------------------------------------------------------
# Type signature vs proof body splitting
# ---------------------------------------------------------------------------


def _split_type_and_body(kind: str, rest_text: str) -> tuple[str, str]:
    """Split a declaration (after its name) into (type_sig, body)."""
    if kind in ("axiom", "constant"):
        return rest_text.strip(), ""

    depth_paren = 0
    depth_brack = 0
    depth_brace = 0
    depth_guil = 0
    in_str = False
    seen_colon = False
    n = len(rest_text)
    i = 0

    while i < n:
        ch = rest_text[i]
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
            depth_paren += 1
        elif ch == ")" and depth_paren > 0:
            depth_paren -= 1
        elif ch == "[":
            depth_brack += 1
        elif ch == "]" and depth_brack > 0:
            depth_brack -= 1
        elif ch in ("{", "⦃"):
            depth_brace += 1
        elif ch in ("}", "⦄") and depth_brace > 0:
            depth_brace -= 1
        elif ch == "«":
            depth_guil += 1
        elif ch == "»" and depth_guil > 0:
            depth_guil -= 1
        elif depth_paren == 0 and depth_brack == 0 and depth_brace == 0 and depth_guil == 0:
            # Check for `:=`
            if ch == ":" and i + 1 < n and rest_text[i + 1] == "=":
                return rest_text[:i].strip(), rest_text[i:].strip()
            # Check for `:` (not `::` or `:=`)
            if ch == ":" and (i + 1 >= n or rest_text[i + 1] not in (":", "=")):
                seen_colon = True
            # Check for `where` keyword
            if (
                ch == "w"
                and rest_text[i : i + 5] == "where"
                and (i == 0 or not (rest_text[i - 1].isalnum() or rest_text[i - 1] == "_"))
                and (i + 5 == n or not (rest_text[i + 5].isalnum() or rest_text[i + 5] == "_"))
            ):
                return rest_text[:i].strip(), rest_text[i:].strip()
            # Check for equation-compiler / inductive constructor `|` at line start or after colon
            if ch == "|" and (seen_colon or kind == "inductive"):
                # Avoid `||` or `|>`
                prev_ch = rest_text[i - 1] if i > 0 else " "
                next_ch = rest_text[i + 1] if i + 1 < n else " "
                if prev_ch in (" ", "\t", "\n") and next_ch in (" ", "\t", "\n"):
                    return rest_text[:i].strip(), rest_text[i:].strip()
        i += 1

    return rest_text.strip(), ""


def _extract_return_type(type_sig: str) -> str:
    """Extract the return type portion after the last top-level `:` in a signature."""
    depth = 0
    colon_pos = -1
    n = len(type_sig)
    i = 0
    while i < n:
        ch = type_sig[i]
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄" and depth > 0:
            depth -= 1
        elif depth == 0 and ch == ":":
            if (i + 1 < n and type_sig[i + 1] in (":", "=")) or (i > 0 and type_sig[i - 1] == ":"):
                i += 2
                continue
            colon_pos = i
            break
        i += 1
    if colon_pos != -1:
        return type_sig[colon_pos + 1 :].strip()
    return type_sig.strip()


# ---------------------------------------------------------------------------
# Bookkeeping classifier
# ---------------------------------------------------------------------------


def is_bookkeeping_decl(
    kind: str,
    short_name: str,
    type_sig: str,
    body: str,
    body_loc: int,
) -> bool:
    """Heuristic classifier for routine Lean glue/bookkeeping declarations."""
    if kind == "instance":
        return True
    if kind in ("structure", "class", "inductive", "axiom", "constant"):
        return False
    if kind in ("def", "abbrev", "opaque"):
        if short_name.startswith(("inst", "coe_", "_aux")) or short_name.endswith(("_aux", "_coe")):
            return True
        return False

    # Theorems / lemmas
    if _BOOKKEEPING_NAME_RE.search(short_name):
        return True

    ret_type = _extract_return_type(type_sig)
    if ret_type and _BOOKKEEPING_RET_TYPE_RE.match(ret_type):
        return True

    if body_loc <= 2 and body and _TRIVIAL_BODY_RE.match(body):
        return True

    return False


# ---------------------------------------------------------------------------
# Identifier extraction
# ---------------------------------------------------------------------------


def extract_identifiers(
    text: str,
    *,
    exclude: set[str] | None = None,
) -> list[str]:
    """Extract unique candidate Lean constant identifiers from text in order of appearance."""
    if not text:
        return []
    seen: set[str] = set()
    out: list[str] = []
    for m in _REF_IDENT_RE.finditer(text):
        tok = m.group(1)
        if tok in seen or tok in LEAN_STOPWORDS:
            continue
        if exclude and tok in exclude:
            continue
        # Skip single-character lowercase variable names (a..z)
        if len(tok) == 1 and tok.islower():
            continue
        seen.add(tok)
        out.append(tok)
    return out


# ---------------------------------------------------------------------------
# Open statement parser
# ---------------------------------------------------------------------------


def _parse_open_targets(rest: str) -> tuple[list[str], bool]:
    """Parse `open ...` remainder into (opened_namespaces, is_local_in)."""
    # Strip parenthesized explicit name lists like `open Foo (bar baz)`
    cleaned = re.sub(r"\([^)]*\)", " ", rest)
    tokens = cleaned.split()
    is_local_in = False
    if tokens and tokens[-1] == "in":
        is_local_in = True
        tokens = tokens[:-1]

    targets: list[str] = []
    skip_next = False
    for tok in tokens:
        if tok in ("scoped", "hiding", "renaming"):
            if tok in ("hiding", "renaming"):
                break
            continue
        if skip_next:
            skip_next = False
            continue
        if tok == "in":
            is_local_in = True
            break
        if re.match(r"^[A-Za-z_][A-Za-z0-9_.]*$", tok):
            targets.append(tok)
    return targets, is_local_in


# ---------------------------------------------------------------------------
# Main Lean 4 file parser
# ---------------------------------------------------------------------------


def parse_lean_source(
    source: str,
    module_path: str,
    *,
    package: str | None = None,
    is_mathlib: bool = False,
) -> ParsedModule:
    """Parse a Lean 4 source file into imports and structured declarations."""
    if package is None:
        package = module_path.split(".", 1)[0] if module_path else ""

    cleaned, docstrings = strip_comments_and_extract_docstrings(source)
    lines = cleaned.splitlines()
    raw_lines = source.splitlines()
    total_loc = sum(1 for ln in lines if ln.strip())

    imports: list[str] = []
    declarations: list[ParsedDecl] = []

    # Scope stack entries: (kind: "namespace"|"section", segments: list[str], open_depth: int)
    scope_stack: list[tuple[str, list[str], int]] = []
    ns_segments: list[str] = []
    open_stack: list[str] = []
    pending_local_opens: list[str] = []

    in_mutual = False
    pending_attr_or_mod_lines: list[int] = []
    in_multiline_attr = False

    # Active declaration accumulator:
    # (kind, decl_raw_name, is_private, start_line, header_rest, ns_tuple, open_tuple, doc, line_indices)
    active: dict | None = None

    def _finalize_active(end_line_1based: int) -> None:
        nonlocal active
        if active is None:
            return
        start_idx = active["start_line"] - 1
        # Trim trailing blank lines from active declaration span
        end_idx = min(end_line_1based - 1, len(lines) - 1)
        while end_idx > start_idx and not lines[end_idx].strip():
            end_idx -= 1

        decl_lines = lines[start_idx : end_idx + 1]
        body_loc = max(1, sum(1 for ln in decl_lines if ln.strip()))

        # Reconstruct declaration text after the declaration name
        rest_lines = [active["first_rest"]] + decl_lines[1:]
        rest_text = "\n".join(rest_lines)

        kind = active["kind"]
        type_sig, body = _split_type_and_body(kind, rest_text)

        # Normalize whitespace in stored type_sig slightly (trim lines, preserve readability)
        type_sig_clean = "\n".join(ln.rstrip() for ln in type_sig.splitlines()).strip()
        c_hash = canonical_type_hash(type_sig_clean)

        short_name = active["short_name"]
        full_name = active["full_name"]
        bk = is_bookkeeping_decl(kind, short_name, type_sig_clean, body, body_loc)

        # Exclude locally bound variables and self-name from extracted references
        binders = set(_extract_binder_names(type_sig_clean))
        binders.add(short_name)
        binders.add(full_name)

        type_refs = extract_identifiers(type_sig_clean, exclude=binders)
        proof_refs = extract_identifiers(body, exclude=binders)

        declarations.append(
            ParsedDecl(
                name=full_name,
                short_name=short_name,
                kind=kind,
                type_sig=type_sig_clean,
                canonical_type_hash=c_hash,
                body_loc=body_loc,
                docstring=active["docstring"],
                is_bookkeeping=bk,
                start_line=active["start_line"],
                end_line=end_idx + 1,
                is_private=active["is_private"],
                namespace_stack=active["ns_tuple"],
                open_namespaces=active["open_tuple"],
                type_refs=type_refs,
                proof_refs=proof_refs,
            )
        )
        active = None

    def _find_attached_docstring(decl_start_line: int) -> str | None:
        if not docstrings:
            return None
        # Look backwards past blank lines and pending attribute/modifier lines
        earliest = pending_attr_or_mod_lines[0] if pending_attr_or_mod_lines else decl_start_line
        probe = earliest - 1
        while probe >= 1:
            if probe in docstrings:
                return docstrings[probe]
            if lines[probe - 1].strip():
                # Hit non-blank code line before finding a docstring
                break
            probe -= 1
        return None

    def _pop_scope(end_name: str | None) -> None:
        if not scope_stack:
            return
        if not end_name:
            skind, segs, open_depth = scope_stack.pop()
            if skind == "namespace" and segs:
                del ns_segments[-len(segs) :]
            del open_stack[open_depth:]
            return

        target_segs = end_name.split(".")
        # Pop matching segments from scope_stack top
        remaining = list(target_segs)
        while remaining and scope_stack:
            skind, segs, open_depth = scope_stack[-1]
            if skind == "section":
                scope_stack.pop()
                del open_stack[open_depth:]
                if segs == remaining:
                    remaining.clear()
                elif segs and len(remaining) >= len(segs) and remaining[-len(segs) :] == segs:
                    del remaining[-len(segs) :]
                continue
            # Namespace frame
            if not segs:
                scope_stack.pop()
                del open_stack[open_depth:]
                continue
            if segs == remaining:
                scope_stack.pop()
                del ns_segments[-len(segs) :]
                del open_stack[open_depth:]
                remaining.clear()
            elif len(segs) > len(remaining) and segs[-len(remaining) :] == remaining:
                # Partial close of `namespace A.B` via `end B`
                k = len(remaining)
                scope_stack[-1] = (skind, segs[:-k], open_depth)
                del ns_segments[-k:]
                remaining.clear()
            elif len(remaining) > len(segs) and remaining[-len(segs) :] == segs:
                scope_stack.pop()
                del ns_segments[-len(segs) :]
                del open_stack[open_depth:]
                del remaining[-len(segs) :]
            else:
                # Mismatched end; pop one frame safely
                scope_stack.pop()
                del ns_segments[-len(segs) :]
                del open_stack[open_depth:]
                break

    mod_short = module_path.rsplit(".", 1)[-1] if module_path else "mod"

    for idx, line in enumerate(lines):
        lineno = idx + 1
        if not line:
            continue

        # Fast-path skip for indented lines (proof tactics, structure fields, continuations)
        first_ch = line[0]
        is_indented = first_ch in (" ", "\t")

        if in_multiline_attr:
            if "]" in line:
                in_multiline_attr = False
            continue

        if is_indented and not in_mutual:
            continue

        stripped = line.lstrip() if in_mutual else line
        if not stripped:
            continue

        # Inside `mutual`, only inspect lines indented <= 2 spaces or `end`
        if in_mutual and is_indented:
            indent = len(line) - len(stripped)
            if indent > 2:
                continue

        # Standalone attribute or modifier line preceding a declaration
        if _ATTR_ONLY_RE.match(stripped) or _MODIFIER_ONLY_RE.match(stripped):
            if active is not None:
                _finalize_active(lineno - 1)
            pending_attr_or_mod_lines.append(lineno)
            continue

        if _ATTR_START_RE.match(stripped) and "]" not in stripped:
            if active is not None:
                _finalize_active(lineno - 1)
            pending_attr_or_mod_lines.append(lineno)
            in_multiline_attr = True
            continue

        # Handle single-line `open Foo in theorem bar ...`
        oidm = _OPEN_IN_DECL_RE.match(stripped)
        if oidm:
            targets, _ = _parse_open_targets(oidm.group(1))
            pending_local_opens.extend(targets)
            stripped = oidm.group(2)

        # Check declaration start
        dm = _DECL_START_RE.match(stripped)
        if dm:
            if active is not None:
                _finalize_active(lineno - 1)

            kind = dm.group(1)
            after_kw = dm.group(2).lstrip()

            # Check if `private` modifier appeared on this line or pending modifier lines
            prefix_part = stripped[: dm.start(1)]
            is_private = bool(re.search(r"\bprivate\b", prefix_part))
            if not is_private and pending_attr_or_mod_lines:
                for pl in pending_attr_or_mod_lines:
                    if re.search(r"\bprivate\b", lines[pl - 1]):
                        is_private = True
                        break

            # Extract declaration name (instances may be anonymous)
            raw_decl_name = ""
            rest_after_name = after_kw
            if kind == "instance":
                # Anonymous instance if starts with `:`, `(`, `[`, `{`, `⦃`, `where`, `:=`
                if after_kw and after_kw[0] not in (":", "(", "[", "{", "⦃"):
                    nm = _IDENT_NAME_RE.match(after_kw)
                    if nm and nm.group(0) not in ("where", "by"):
                        raw_decl_name = nm.group(1) or nm.group(2)
                        rest_after_name = after_kw[nm.end() :]
                if not raw_decl_name:
                    raw_decl_name = f"inst_{mod_short}_L{lineno}"
            else:
                nm = _IDENT_NAME_RE.match(after_kw)
                if nm:
                    raw_decl_name = nm.group(1) or nm.group(2)
                    rest_after_name = after_kw[nm.end() :]
                else:
                    raw_decl_name = f"anon_{kind}_{mod_short}_L{lineno}"

            # Strip optional universe params `.{u, v}` right after name
            if rest_after_name.startswith(".{"):
                close_u = rest_after_name.find("}")
                if close_u != -1:
                    rest_after_name = rest_after_name[close_u + 1 :]

            # Compute full qualified name & short_name
            if raw_decl_name.startswith("_root_."):
                clean_raw = raw_decl_name[7:]
                full_name = clean_raw
            elif ns_segments:
                full_name = ".".join(ns_segments) + "." + raw_decl_name
            else:
                full_name = raw_decl_name

            short_name = full_name.rsplit(".", 1)[-1]
            doc = _find_attached_docstring(lineno)
            pending_attr_or_mod_lines.clear()

            combined_opens = tuple(open_stack + pending_local_opens)
            pending_local_opens.clear()

            active = {
                "kind": kind,
                "full_name": full_name,
                "short_name": short_name,
                "is_private": is_private,
                "start_line": lineno,
                "first_rest": rest_after_name,
                "ns_tuple": tuple(ns_segments),
                "open_tuple": combined_opens,
                "docstring": doc,
            }
            continue

        # Not a declaration start — check structural top-level commands
        if not is_indented:
            # Handle `open ... in <decl>` on a single line? Usually `open ... in` is on its own line.
            im = _IMPORT_RE.match(stripped)
            if im:
                if active is not None:
                    _finalize_active(lineno - 1)
                imports.append(im.group(1))
                pending_attr_or_mod_lines.clear()
                continue

            nsm = _NAMESPACE_RE.match(stripped)
            if nsm:
                if active is not None:
                    _finalize_active(lineno - 1)
                segs = nsm.group(1).split(".")
                scope_stack.append(("namespace", segs, len(open_stack)))
                ns_segments.extend(segs)
                pending_attr_or_mod_lines.clear()
                continue

            secm = _SECTION_RE.match(stripped)
            if secm:
                if active is not None:
                    _finalize_active(lineno - 1)
                segs = secm.group(1).split(".") if secm.group(1) else []
                scope_stack.append(("section", segs, len(open_stack)))
                pending_attr_or_mod_lines.clear()
                continue

            if _MUTUAL_RE.match(stripped):
                if active is not None:
                    _finalize_active(lineno - 1)
                in_mutual = True
                pending_attr_or_mod_lines.clear()
                continue

            em = _END_RE.match(stripped)
            if em:
                if active is not None:
                    _finalize_active(lineno - 1)
                if in_mutual and not em.group(1):
                    in_mutual = False
                else:
                    _pop_scope(em.group(1))
                pending_attr_or_mod_lines.clear()
                continue

            om = _OPEN_RE.match(stripped)
            if om:
                if active is not None:
                    _finalize_active(lineno - 1)
                targets, is_local_in = _parse_open_targets(om.group(1))
                if is_local_in:
                    pending_local_opens.extend(targets)
                else:
                    open_stack.extend(targets)
                pending_attr_or_mod_lines.clear()
                continue

            if _TOP_COMMAND_RE.match(stripped):
                if active is not None:
                    _finalize_active(lineno - 1)
                pending_attr_or_mod_lines.clear()
                continue

    if active is not None:
        _finalize_active(len(lines))

    return ParsedModule(
        path=module_path,
        package=package,
        loc=total_loc,
        is_mathlib=is_mathlib,
        imports=imports,
        declarations=declarations,
    )
