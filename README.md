# proof-compressor

Compress, analyze, audit, and expose massive Lean 4 proof repositories into human-readable mathematics, interactive proof blueprints, and kernel-checked refactoring plans.

## System Overview (5 Stages)

1. **Lean 4 `.olean` Kernel Extractor (`lean_extractor/`, `proof_compressor.ingest.olean_bridge`)**
   - Self-contained Lean 4 metaprogram (`ExtractDag.lean`) that loads a compiled `Environment`, walks `Expr.getUsedConstants` from target roots stopping at Mathlib/Init/Std/Lean boundaries, collects kernel proof-term sizes and `#print axioms` footprints, and emits JSONL directly into SQLite.
2. **Zero-Extraction Streaming Source Ingestor (`proof_compressor.ingest`, `proof_compressor.schema`)**
   - Streams `.lean` sources straight from directories, `.tar.gz`, or multi-part `.tar.gz.part01..N` archives directly into a WAL-tuned SQLite dependency graph with zero disk extraction, two-pass transitive import resolution, alpha-equivalent `canonical_type_hash`, and bookkeeping heuristics.
3. **Graph Pruning, Deduplication, Topology & Clustering (`proof_compressor.analyze`)**
   - **Reachability pruning (`prune.py`)**: Exact reverse-dependency traversal from explicit or auto-detected `Main`/`Statements` roots with Mathlib boundary isolation.
   - **Deduplication (`dedup.py`)**: Exact `canonical_type_hash` groups, alpha/namespace-normalized near-duplicates, isomorphic definitions, and Mathlib-absorption candidates.
   - **Scalable topology (`topology.py`)**: Pure-stdlib CSR graphs with iterative Tarjan SCC, iterative Cooper–Harvey–Kennedy dominator trees, exact/landmark-sketch DAG flow, bottleneck scoring, and transitively reduced pillar backbones (500k nodes / 2M edges in ~4.5s).
   - **Modular clustering (`cluster.py`)**: Hierarchical chapter/section DAG clustering with exact `Inputs ⊢ Outputs` interfaces.
4. **Mathematical Exposition & Fidelity Auditing (`proof_compressor.expose`)**
   - **Symbol registry & filtering (`symbols.py`, `filter.py`)**: Maps high-centrality Lean declarations to consistent standard mathematical notation, collapses Lean bookkeeping glue, and tags cluster proof idioms.
   - **Annals-style LaTeX (`latex.py`)**: Deterministic, offline synthesis of `paper.tex` with `\leanlink{...}` anchors and an optional guarded LLM refinement hook.
   - **Interactive 3-Zoom Blueprint (`blueprint.html` via `blueprint.py`)**: Self-contained zero-build HTML proof map (Level 0 bottleneck/chapter DAG, Level 1 KaTeX chapters with formal interfaces, Level 2 Lean declaration & dependency inspector).
   - **Automated Auditor (`audit.py`)**: Verifies every `\leanlink` exists and is reachable, checks all prose proof citations lie in the Lean dependency DAG, detects omitted high-bottleneck dependencies, dropped hypotheses, symbol drift, and Lean bookkeeping leaks.
5. **Kernel-Checked Refactoring Engine (`proof_compressor.refactor`)**
   - **Planner (`planner.py`)**: Ranks high-leverage refactoring targets by internal LOC, interface narrowness, duplication, and Mathlib-absorption potential, emitting self-contained `Inputs ⊢ Outputs` work orders.
   - **Verification gate (`gate.py`)**: Enforces `lake build`, `#print axioms` invariance, exported signature preservation, and strict LOC reduction.

## Quickstart

### Python CLI (`uv`)

```bash
uv sync
uv run proof-compressor --help

# Run the full pipeline on a multi-part archive (zero disk extraction)
uv run proof-compressor run-all data/lean.tar.gz.part01 \
  --db outputs/proof.db \
  --out outputs/exposition

# Or run stages individually
uv run proof-compressor ingest data/lean.tar.gz.part01 --db outputs/proof.db
uv run proof-compressor analyze --db outputs/proof.db
uv run proof-compressor stats --db outputs/proof.db
uv run proof-compressor bottlenecks --db outputs/proof.db --top-k 25
uv run proof-compressor expose --db outputs/proof.db --out outputs/exposition
uv run proof-compressor audit --db outputs/proof.db --tex outputs/exposition/paper.tex
uv run proof-compressor refactor-plan --db outputs/proof.db --out outputs/exposition/refactor_plan.md

# Run the test suite
uv run pytest
```

### Lean 4 Kernel Extractor (`~/.elan/bin/lake`)

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd lean_extractor
lake build

# Self-test on built-in demo theorem and ingest into SQLite
lake env .lake/build/bin/extract_dag --self-test --out /tmp/demo_dag.jsonl
cd ..
uv run proof-compressor ingest-olean /tmp/demo_dag.jsonl --db /tmp/demo.db
```

## Full-Scale Benchmark: `alpo.ge` Riemann Hypothesis Proof

End-to-end zero-extraction run over the complete 14-part `alpo.ge` Lean 4 formalization (`lean.tar.gz.part01..part14`, 239.3 MB compressed / 1.031 GB uncompressed, auto-detecting all 5 root theorems in `Main.lean`: `riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`):

| Metric | Raw Corpus | Reachable Core | Compression / Notes |
|---|---:|---:|---|
| Lean modules | 175,187 | 35,669 | **-79.6%** (139,518 dead modules pruned) |
| Project LOC | 15,531,759 | 3,534,659 | **-77.2%** (**4.39x** lossless pruning) |
| Declarations | 1,061,425 | 183,501 | **-82.7%** (955,634 reachable / 7,541,179 raw edges) |
| Est. post-dedup body LOC | 2,252,399 (reachable) | 1,597,336 | **-29.1%** further (~9.7x cumulative from raw LOC) |
| End-to-end wall-clock | — | **467 s** (~7.8 min) | Ingest 343.4s, Analyze 31.9s, Expose/Audit/Refactor ~90s |
| Peak RSS / SQLite DB | — | **3.72 GiB** / **1.5 GB** | **0** `.lean` files unpacked to disk |
| Exposition audit fidelity | — | **1.0000 (PASS)** | **757** unique (`1,128` total) verified `\leanlink` anchors, **149/149** theorems/proofs audited, **0** issues across all 7 checks |

Deduplication & Mathlib absorption on the 183,501 reachable declarations identified **13,694** exact duplicate groups (`197,394` LOC), **10,910** near-duplicate groups (`166,594` LOC), **5,429** isomorphic definition groups, and **39,972** Mathlib-absorption candidates (`358,633` LOC). Top extracted mathematical bottlenecks recover the core pillars of Alpöge's `remark.pdf` (Jacquet–Rallis relative trace formula / Fourier-orbital matching, abelian variety Theorem of the Cube / isogenies / torsion & Weil bounds, étale cohomology / Galois local-global & p-adic tilting structures, and the root GRH assembly chain).

### Sample Outputs (`examples/rh_alpo/`)

- [paper.tex](examples/rh_alpo/paper.tex) — 12-chapter Annals-style LaTeX manuscript (157 KB, 2,215 lines, 757 unique `\leanlink` anchors).
- [blueprint.html](examples/rh_alpo/blueprint.html) — Interactive 3-zoom-level proof DAG, KaTeX chapter explorer, and Lean declaration inspector (427 KB).
- [audit_report.md](examples/rh_alpo/audit_report.md) / [audit_report.json](examples/rh_alpo/audit_report.json) — Automated statement/dependency audit (`PASS`, fidelity `1.0000`, 0 issues).
- [refactor_plan.md](examples/rh_alpo/refactor_plan.md) — Top 20 ranked Stage 4 refactoring work orders.
