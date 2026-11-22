"""Grounded manuscript engine: per-domain dossiers and multi-chapter manuscript assembly.

Two jobs:

1. ``build_dossier`` collects everything an author needs to write one chapter
   from ground truth: the top bottleneck declarations in a set of module
   prefixes, their docstrings and signatures, their direct reachable
   dependencies, and (optionally) the verbatim Lean source of the selected
   modules streamed out of the archive without unpacking it.
2. ``assemble_manuscript`` stitches hand-written chapter fragments into one
   compilable ``manuscript.tex`` with a shared preamble, a symbol guide, and a
   Lean concordance appendix generated from the ``\\leanlink`` anchors actually
   used in the chapters.
"""

from __future__ import annotations

import json
import re
import sqlite3
import tarfile
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence

from proof_compressor.expose._db import DbHandle, open_db, query_all
from proof_compressor.expose.symbols import escape_latex_text

_LEANLINK_RE = re.compile(r"\\leanlink(?:\[[^\]]*\])?\{([^}]+)\}")

# ---------------------------------------------------------------------------
# Archive streaming
# ---------------------------------------------------------------------------


class _ConcatReader:
    """File-like object reading several files back to back (multi-part archives)."""

    def __init__(self, paths: Sequence[Path]) -> None:
        self._paths = list(paths)
        self._idx = 0
        self._fh = open(self._paths[0], "rb") if self._paths else None

    def read(self, size: int = -1) -> bytes:
        if self._fh is None:
            return b""
        chunks: list[bytes] = []
        remaining = size
        while self._fh is not None and (remaining < 0 or remaining > 0):
            data = self._fh.read(remaining if remaining > 0 else -1)
            if data:
                chunks.append(data)
                if remaining > 0:
                    remaining -= len(data)
                continue
            self._fh.close()
            self._idx += 1
            self._fh = open(self._paths[self._idx], "rb") if self._idx < len(self._paths) else None
        return b"".join(chunks)

    def close(self) -> None:
        if self._fh is not None:
            self._fh.close()
            self._fh = None


def resolve_archive_parts(source: str | Path) -> list[Path]:
    """Resolve a `.tar.gz`, a `.part01` (auto-discovering siblings), or a glob into ordered paths."""
    p = Path(source)
    m = re.match(r"^(.*\.part)(\d+)$", p.name)
    if m:
        prefix, width = m.group(1), len(m.group(2))
        parts = sorted(p.parent.glob(f"{prefix}{'[0-9]' * width}"))
        return parts
    if any(ch in str(source) for ch in "*?["):
        return sorted(Path().glob(str(source)))
    return [p]


def module_to_member_suffix(module_path: str) -> str:
    """`Supplements.Kernels.MainTheorems` -> `Supplements/Kernels/MainTheorems.lean`."""
    return module_path.replace(".", "/") + ".lean"


def stream_module_sources(
    archive: str | Path,
    module_paths: Iterable[str],
    *,
    src_prefixes: Sequence[str] = ("lean/src/", "src/", ""),
) -> dict[str, str]:
    """Stream an archive and return the text of only the requested modules (no disk extraction).

    Stops as soon as every requested module has been found.
    """
    wanted = {module_to_member_suffix(m): m for m in module_paths}
    found: dict[str, str] = {}
    if not wanted:
        return found
    parts = resolve_archive_parts(archive)
    reader = _ConcatReader(parts)
    try:
        with tarfile.open(fileobj=reader, mode="r|gz") as tf:
            for member in tf:
                if not member.isfile() or not member.name.endswith(".lean"):
                    continue
                name = member.name
                for pref in src_prefixes:
                    if pref and not name.startswith(pref):
                        continue
                    rel = name[len(pref):]
                    mod = wanted.get(rel)
                    if mod is not None and mod not in found:
                        fh = tf.extractfile(member)
                        if fh is not None:
                            found[mod] = fh.read().decode("utf-8", errors="replace")
                        break
                if len(found) == len(wanted):
                    break
    finally:
        reader.close()
    return found


def extract_declaration_source(module_text: str, start_line: int, end_line: int, *, context: int = 0) -> str:
    """Slice a declaration's source lines (1-based, inclusive) out of a module text."""
    lines = module_text.splitlines()
    lo = max(0, start_line - 1 - context)
    hi = min(len(lines), max(end_line, start_line) + context)
    return "\n".join(lines[lo:hi])


# ---------------------------------------------------------------------------
# Dossiers
# ---------------------------------------------------------------------------


@dataclass
class DossierEntry:
    """One declaration selected for a chapter dossier."""

    decl_id: int
    name: str
    kind: str
    module_path: str
    type_sig: str
    docstring: str
    body_loc: int
    bottleneck_score: float
    start_line: int
    end_line: int
    direct_deps: list[str] = field(default_factory=list)
    source: str = ""

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class Dossier:
    """Ground-truth material for one chapter."""

    title: str
    module_prefixes: list[str]
    entries: list[DossierEntry] = field(default_factory=list)
    module_sources: dict[str, str] = field(default_factory=dict)
    stats: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "title": self.title,
            "module_prefixes": self.module_prefixes,
            "stats": self.stats,
            "entries": [e.to_dict() for e in self.entries],
            "module_sources": self.module_sources,
        }

    def to_markdown(self, *, max_source_lines: int = 40) -> str:
        lines = [f"# Dossier: {self.title}", ""]
        lines.append(f"Module prefixes: {', '.join(self.module_prefixes) or '(explicit names)'}")
        for k, v in self.stats.items():
            lines.append(f"- {k}: {v}")
        lines.append("")
        for e in self.entries:
            lines.append(f"## `{e.name}` ({e.kind}, score {e.bottleneck_score:.2f}, {e.body_loc} LOC)")
            lines.append(f"Module: `{e.module_path}` lines {e.start_line}-{e.end_line}")
            if e.docstring:
                lines.append(f"> {' '.join(e.docstring.split())}")
            lines.append("```lean")
            lines.append(e.type_sig.strip()[:800])
            lines.append("```")
            if e.direct_deps:
                lines.append("Direct reachable deps: " + ", ".join(f"`{d}`" for d in e.direct_deps))
            if e.source:
                src_lines = e.source.splitlines()[:max_source_lines]
                lines.append("```lean")
                lines.extend(src_lines)
                lines.append("```")
            lines.append("")
        return "\n".join(lines)


def _prefix_clause(prefixes: Sequence[str]) -> tuple[str, list[str]]:
    if not prefixes:
        return "1=1", []
    clause = " OR ".join("mod.path LIKE ?" for _ in prefixes)
    return f"({clause})", [p.rstrip(".") + "%" for p in prefixes]


def build_dossier(
    db: DbHandle,
    *,
    title: str,
    module_prefixes: Sequence[str] = (),
    decl_names: Sequence[str] = (),
    top_k: int = 30,
    kinds: Sequence[str] = ("theorem", "lemma", "def", "structure", "class", "inductive", "abbrev"),
    archive: str | Path | None = None,
    max_deps: int = 10,
    include_bookkeeping: bool = False,
) -> Dossier:
    """Collect the top reachable declarations of a domain plus their deps and verbatim Lean source."""
    with open_db(db) as conn:
        rows: list[dict[str, Any]] = []
        seen: set[int] = set()
        if decl_names:
            ph = ",".join("?" for _ in decl_names)
            for r in query_all(
                conn,
                f"""
                SELECT d.id, d.name, d.kind, d.type_sig, COALESCE(d.docstring,'') AS docstring,
                       d.body_loc, d.start_line, d.end_line, mod.path AS module_path,
                       COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score
                FROM declarations d
                JOIN modules mod ON mod.id = d.module_id
                LEFT JOIN metrics m ON m.decl_id = d.id
                WHERE d.name IN ({ph})
                """,
                tuple(decl_names),
            ):
                rows.append(r)
                seen.add(int(r["id"]))
        if module_prefixes and top_k > 0:
            clause, params = _prefix_clause(module_prefixes)
            kph = ",".join("?" for _ in kinds)
            bk = "" if include_bookkeeping else "AND d.is_bookkeeping = 0"
            for r in query_all(
                conn,
                f"""
                SELECT d.id, d.name, d.kind, d.type_sig, COALESCE(d.docstring,'') AS docstring,
                       d.body_loc, d.start_line, d.end_line, mod.path AS module_path,
                       COALESCE(m.bottleneck_score, 0.0) AS bottleneck_score
                FROM declarations d
                JOIN modules mod ON mod.id = d.module_id
                JOIN metrics m ON m.decl_id = d.id
                WHERE m.reachable = 1 AND d.is_mathlib = 0 {bk}
                  AND d.kind IN ({kph}) AND {clause}
                ORDER BY m.bottleneck_score DESC, d.body_loc DESC
                LIMIT ?
                """,
                (*kinds, *params, top_k),
            ):
                if int(r["id"]) not in seen:
                    rows.append(r)
                    seen.add(int(r["id"]))

        entries: list[DossierEntry] = []
        for r in rows:
            deps = query_all(
                conn,
                """
                SELECT DISTINCT d.name
                FROM edges e
                JOIN declarations d ON d.id = e.dst_id
                LEFT JOIN metrics m ON m.decl_id = d.id
                WHERE e.src_id = ? AND d.id != ? AND d.is_mathlib = 0
                ORDER BY COALESCE(m.bottleneck_score, 0) DESC
                LIMIT ?
                """,
                (int(r["id"]), int(r["id"]), max_deps),
            )
            entries.append(
                DossierEntry(
                    decl_id=int(r["id"]),
                    name=str(r["name"]),
                    kind=str(r["kind"] or ""),
                    module_path=str(r["module_path"] or ""),
                    type_sig=str(r["type_sig"] or ""),
                    docstring=str(r["docstring"] or ""),
                    body_loc=int(r["body_loc"] or 0),
                    bottleneck_score=float(r["bottleneck_score"] or 0.0),
                    start_line=int(r["start_line"] or 0),
                    end_line=int(r["end_line"] or 0),
                    direct_deps=[str(d["name"]) for d in deps],
                )
            )

        stats: dict[str, Any] = {"selected_declarations": len(entries)}
        if module_prefixes:
            clause, params = _prefix_clause(module_prefixes)
            agg = query_all(
                conn,
                f"""
                SELECT COUNT(DISTINCT mod.id) AS modules, COUNT(d.id) AS decls,
                       COALESCE(SUM(d.body_loc),0) AS body_loc
                FROM declarations d
                JOIN modules mod ON mod.id = d.module_id
                JOIN metrics m ON m.decl_id = d.id
                WHERE m.reachable = 1 AND d.is_mathlib = 0 AND {clause}
                """,
                tuple(params),
            )
            if agg:
                stats.update({f"reachable_{k}": v for k, v in agg[0].items()})

    dossier = Dossier(title=title, module_prefixes=list(module_prefixes), entries=entries, stats=stats)

    if archive is not None and entries:
        mods = sorted({e.module_path for e in entries if e.module_path})
        sources = stream_module_sources(archive, mods)
        dossier.module_sources = sources
        for e in entries:
            text = sources.get(e.module_path)
            if text and e.start_line > 0:
                e.source = extract_declaration_source(text, e.start_line, e.end_line)
    return dossier


# ---------------------------------------------------------------------------
# Manuscript assembly
# ---------------------------------------------------------------------------

MANUSCRIPT_PREAMBLE = r"""\documentclass[11pt,reqno]{amsart}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{newunicodechar}
\newunicodechar{₂}{\textsubscript{2}}
\usepackage{amsmath,amssymb,amsthm,mathtools,array}
\usepackage{booktabs,longtable}
\usepackage{xcolor}
\usepackage[margin=1.1in]{geometry}
\usepackage[colorlinks=true,linkcolor=blue!50!black,citecolor=blue!50!black,urlcolor=blue!50!black]{hyperref}
\setcounter{tocdepth}{1}

\theoremstyle{plain}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem*{maintheorem}{Main Theorem}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{remark}[theorem]{Remark}
\newtheorem{example}[theorem]{Example}

% Formal anchors: a small, line-breakable pointer to the exact Lean constant.
\makeatletter
\g@addto@macro\UrlSpecials{\do\₂{\textnormal{\textsubscript{2}}}}
\makeatother
\newcommand{\leanlink}[1]{\allowbreak{\tiny\texttt{[\expandafter\nolinkurl\expandafter{\detokenize{#1}}]}}}
\newcommand{\leanmod}[1]{\allowbreak{\scriptsize\texttt{\expandafter\nolinkurl\expandafter{\detokenize{#1}}}}}

% Shared notation
\newcommand{\C}{\mathbb{C}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\A}{\mathbb{A}}
\newcommand{\F}{\mathbb{F}}
\DeclareMathOperator{\re}{Re}
\DeclareMathOperator{\im}{Im}
\DeclareMathOperator{\Gal}{Gal}
\DeclareMathOperator{\GL}{GL}
\DeclareMathOperator{\SL}{SL}
\DeclareMathOperator{\U}{U}
\DeclareMathOperator{\End}{End}
\DeclareMathOperator{\Hom}{Hom}
\DeclareMathOperator{\Spec}{Spec}
\DeclareMathOperator{\Pic}{Pic}
\DeclareMathOperator{\ord}{ord}
\DeclareMathOperator{\vol}{vol}
\DeclareMathOperator{\tr}{tr}

\emergencystretch=3em
"""


def collect_leanlinks(tex: str) -> list[str]:
    """Return unique `\\leanlink` constants in first-appearance order."""
    seen: dict[str, None] = {}
    for m in _LEANLINK_RE.finditer(tex):
        seen.setdefault(m.group(1).strip(), None)
    return list(seen)


def _concordance_rows(conn: sqlite3.Connection, names: Sequence[str]) -> list[dict[str, Any]]:
    if not names:
        return []
    out: dict[str, dict[str, Any]] = {}
    for i in range(0, len(names), 400):
        batch = list(names[i : i + 400])
        ph = ",".join("?" for _ in batch)
        for r in query_all(
            conn,
            f"""
            SELECT d.name, d.kind, mod.path AS module_path, d.body_loc,
                   COALESCE(m.bottleneck_score, 0.0) AS score
            FROM declarations d
            JOIN modules mod ON mod.id = d.module_id
            LEFT JOIN metrics m ON m.decl_id = d.id
            WHERE d.name IN ({ph})
            """,
            tuple(batch),
        ):
            out[str(r["name"])] = r
    return [out[n] for n in names if n in out]


def build_concordance_appendix(
    db: DbHandle,
    chapter_texts: Sequence[str],
    *,
    max_rows: int = 200,
) -> str:
    """Generate a longtable mapping theorem-environment anchors to kind, module, and size."""
    block_re = re.compile(
        r"\\begin\{(theorem|proposition|lemma|corollary|definition|maintheorem)\}(.*?)\\end\{\1\}",
        re.S,
    )
    anchored: dict[str, None] = {}
    for t in chapter_texts:
        for m in block_re.finditer(t):
            link_m = _LEANLINK_RE.search(m.group(2))
            if link_m is not None:
                anchored.setdefault(link_m.group(1).strip(), None)
    names = list(anchored)[:max_rows]
    with open_db(db) as conn:
        rows = _concordance_rows(conn, names)
    lines = [
        r"\section{Formal Verification and Lean Concordance}",
        r"\label{app:lean-concordance}",
        "Every formal statement in the body of this paper corresponds to a kernel-checked "
        "Lean declaration in the reachable dependency cone of \\leanmod{Main}. "
        "The table below maps each anchored theorem, proposition, lemma, corollary, or "
        "definition to its Lean declaration kind, defining module, and formal proof length "
        "in lines of code (LOC).",
        "",
        r"{\small",
        r"\begin{longtable}{@{}p{0.40\textwidth}lp{0.38\textwidth}r@{}}",
        r"\toprule",
        r"Lean constant & Kind & Module & LOC \\",
        r"\midrule",
        r"\endhead",
    ]
    for r in rows:
        lines.append(
            f"\\raggedright\\leanlink{{{r['name']}}} & {escape_latex_text(str(r['kind']))} & "
            f"\\raggedright{{\\tiny\\texttt{{\\expandafter\\nolinkurl\\expandafter{{\\detokenize{{{r['module_path']}}}}}}}}} & {int(r['body_loc'] or 0):,} \\\\"
        )
    lines += [r"\bottomrule", r"\end{longtable}", "}", ""]
    return "\n".join(lines)


def assemble_manuscript(
    db: DbHandle,
    chapter_paths: Sequence[str | Path],
    output_path: str | Path,
    *,
    title: str,
    author: str,
    abstract: str,
    short_title: str = "",
    front_matter: str = "",
    back_matter: str = "",
    include_concordance: bool = True,
) -> str:
    """Stitch chapter fragments into one compilable manuscript with a concordance appendix."""
    chapter_texts: list[str] = []
    for p in chapter_paths:
        txt = Path(p).read_text(encoding="utf-8")
        txt = re.sub(r"\\documentclass.*?\\begin\{document\}", "", txt, flags=re.S)
        txt = txt.replace(r"\end{document}", "")
        chapter_texts.append(txt.strip())

    title_cmd = f"\\title[{short_title}]{{{title}}}" if short_title else f"\\title{{{title}}}"
    parts = [
        MANUSCRIPT_PREAMBLE,
        title_cmd,
        f"\\author{{{author}}}",
        r"\date{\today}",
        "",
        r"\begin{document}",
        r"\begin{abstract}",
        abstract.strip(),
        r"\end{abstract}",
        r"\maketitle",
        r"\tableofcontents",
        "",
    ]
    if front_matter:
        parts.append(front_matter.strip())
        parts.append("")
    for t in chapter_texts:
        parts.append(f"% {'-' * 70}")
        parts.append(t)
        parts.append("")
    parts.append(r"\appendix")
    if back_matter:
        parts.append(back_matter.strip())
        parts.append("")
    if include_concordance:
        parts.append(build_concordance_appendix(db, chapter_texts))
    parts.append(r"\end{document}")
    out_text = "\n".join(parts) + "\n"
    out = Path(output_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(out_text, encoding="utf-8")
    return out_text


def check_chapter_links(db: DbHandle, tex: str) -> dict[str, list[str]]:
    """Quick pre-audit: list `\\leanlink`s that are unknown or unreachable."""
    names = collect_leanlinks(tex)
    unknown: list[str] = []
    unreachable: list[str] = []
    with open_db(db) as conn:
        known: dict[str, int] = {}
        for i in range(0, len(names), 400):
            batch = names[i : i + 400]
            ph = ",".join("?" for _ in batch)
            for r in query_all(
                conn,
                f"""SELECT d.name, COALESCE(m.reachable, 0) AS reachable
                    FROM declarations d LEFT JOIN metrics m ON m.decl_id = d.id
                    WHERE d.name IN ({ph})""",
                tuple(batch),
            ):
                known[str(r["name"])] = int(r["reachable"])
    for n in names:
        if n not in known:
            unknown.append(n)
        elif known[n] == 0:
            unreachable.append(n)
    return {"links": names, "unknown": unknown, "unreachable": unreachable}


def write_dossier(dossier: Dossier, out_dir: str | Path, stem: str) -> tuple[Path, Path]:
    """Persist a dossier as JSON + Markdown."""
    d = Path(out_dir)
    d.mkdir(parents=True, exist_ok=True)
    jp = d / f"{stem}.json"
    mp = d / f"{stem}.md"
    jp.write_text(json.dumps(dossier.to_dict(), indent=2), encoding="utf-8")
    mp.write_text(dossier.to_markdown(), encoding="utf-8")
    return jp, mp


def iter_chapter_paths(chapters_dir: str | Path) -> Iterator[Path]:
    """Yield `chNN_*.tex` chapter fragments in order."""
    yield from sorted(Path(chapters_dir).glob("ch[0-9][0-9]_*.tex"))
