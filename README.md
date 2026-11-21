# proof-compressor

Compress, analyze, audit, materialize, and expose massive Lean 4 proof repositories into human-readable mathematics, interactive proof blueprints, compilable pruned Lean projects, and kernel-checked refactoring plans.

## System Overview (5 Stages)

1. **Lean 4 `.olean` Kernel Extractor (`lean_extractor/`, `proof_compressor.ingest.olean_bridge`)**
   - Self-contained Lean 4 metaprogram (`ExtractDag.lean`) that loads a compiled `Environment`, walks `Expr.getUsedConstants` from target roots stopping at Mathlib/Init/Std/Lean boundaries, collects kernel proof-term sizes and `#print axioms` footprints, and emits JSONL directly into SQLite.
2. **Zero-Extraction Streaming Source Ingestor (`proof_compressor.ingest`, `proof_compressor.schema`)**
   - Streams `.lean` sources straight from directories, `.tar.gz`, or multi-part `.tar.gz.part01..N` archives directly into a WAL-tuned SQLite dependency graph with zero disk extraction, two-pass transitive import resolution, alpha-equivalent `canonical_type_hash`, and bookkeeping heuristics.
3. **Graph Pruning, Compilable Materialization, Deduplication, Topology & Clustering (`proof_compressor.analyze`)**
   - **Reachability pruning (`prune.py`)**: Exact reverse-dependency traversal from explicit or auto-detected `Main`/`Statements` roots with Mathlib boundary isolation.
   - **Compilable Lean 4 materialization (`materialize.py`)**: Stream-materializes a pruned, import-rewritten, dead-lemma-stripped Lean 4 project in three modes:
     - `instance-aware` *(compilable default)*: keeps all declaration-reachable modules plus any transitively imported `instance`/`class`/bridge support modules, rewrites `import` headers to eliminate dead side-imports, and strips unreferenced intra-module theorems/lemmas.
     - `decl-exact`: keeps only declaration-reachable modules and strips dead intra-module theorems/lemmas.
     - `import-closure`: keeps the full transitive module-import closure while stripping dead intra-module theorems/lemmas.
   - **Deduplication (`dedup.py`)**: Exact `canonical_type_hash` groups, alpha/namespace-normalized near-duplicates, isomorphic definitions, and Mathlib-absorption candidates.
   - **Scalable topology (`topology.py`)**: Pure-stdlib CSR graphs with iterative Tarjan SCC, iterative Cooper–Harvey–Kennedy dominator trees, exact/landmark-sketch DAG flow, bottleneck scoring, and transitively reduced pillar backbones (500k nodes / 2M edges in ~4.5s).
   - **Modular clustering (`cluster.py`)**: Hierarchical chapter/section DAG clustering with exact `Inputs ⊢ Outputs` interfaces.
4. **Mathematical Exposition & Fidelity Auditing (`proof_compressor.expose`)**
   - **Symbol registry & filtering (`symbols.py`, `filter.py`)**: Maps high-centrality Lean declarations to consistent standard mathematical notation, collapses Lean bookkeeping glue, and tags cluster proof idioms.
   - **Annals-style LaTeX & Compiled PDF (`latex.py`)**: Deterministic, offline synthesis of `paper.tex` (compilable to `paper.pdf` via `tectonic` with zero TeX errors), complete with `\leanlink{...}` anchors and an optional guarded LLM refinement hook.
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

# Compute or materialize a compilable pruned Lean 4 project
uv run proof-compressor materialize --db outputs/proof.db --mode instance-aware --dry-run
uv run proof-compressor materialize --db outputs/proof.db \
  --source data/lean.tar.gz.part01 \
  --out outputs/pruned_lean_project \
  --mode instance-aware

# Run the test suite (33 tests including real lake build & #print axioms checks)
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

| Metric | Raw Corpus | Reachable / Materialized Core | Compression / Notes |
|---|---:|---:|---|
| Lean modules (`decl-exact`) | 175,187 | 35,669 | **-79.64%** (139,518 dead modules pruned) |
| Lean modules (`instance-aware` compilable) | 175,187 | 39,847 | **-77.25%** (+4,088 transitive `instance`/`class` support + 90 bridges) |
| Project LOC (module-level reachable) | 15,531,759 | 3,534,659 | **-77.24%** (**4.39x** lossless module pruning) |
| Materialized LOC (`instance-aware` + dead-lemma strip) | 15,531,759 | 3,321,148 | **-78.62%** (strips 92,677 dead intra-module lemmas / -941,721 LOC) |
| Materialized LOC (`decl-exact` + dead-lemma strip) | 15,531,759 | 2,895,538 | **-81.36%** (strips 64,572 dead intra-module lemmas / -639,121 LOC) |
| Declarations | 1,061,425 | 183,501 | **-82.71%** (955,634 reachable / 7,541,179 raw edges) |
| Est. post-dedup body LOC | 2,252,399 (reachable) | 1,597,336 | **-29.08%** further (~9.7x cumulative from raw LOC) |
| End-to-end wall-clock | — | **467 s** (~7.8 min) | Ingest 343.4s, Analyze 31.9s, Expose/Audit/Refactor ~90s |
| Peak RSS / SQLite DB | — | **3.72 GiB** / **1.5 GB** | **0** `.lean` files unpacked to disk |
| Exposition audit fidelity | — | **1.0000 (PASS)** | **769** unique (`1,128` total) verified `\leanlink` anchors, **149/149** theorems/proofs audited, **0** issues across all 7 checks |

### Full-Corpus Soundness & Why Module-Import Closure Was 175,184 Modules

- **Full-corpus soundness audit**: Streaming scan across all **175,187 `.lean` files (15,531,759 lines)** verified **0 `sorry`**, **0 `admit`**, **0 custom `axiom`**, **0 `opaque`**, **0 `constant`**, **0 `unsafe`**, and **0 `native_decide`** declarations. In `Main.lean`'s compilation check, `#print axioms` confirms all 5 root theorems depend only on standard Lean axioms (`propext`, `Quot.sound`).
- **Why `Main.lean`'s raw `import` closure pulled in 175,184 of 175,187 modules**:
  1. **Umbrella barrel side-imports**: `Supplements.Kernels.MainTheoremsAll` and `MainTheoremsCritical` define zero declarations of their own, yet import 4 unused `SmallClassNumbers.*` modules (`CorGKOf` alone transitively pulls in **170,699 modules** via module imports even though `Main.lean` never references `CorGKOf`).
  2. **Over-wide file import headers**: The 35,669 declaration-reachable modules contain **10,255 unused `import` lines** that were only needed by dead intra-module declarations.
  3. **Breakdown of the 139,515 imported-but-unreached modules (`11,996,775` LOC)**: **80,676** pure unused theorem/lemma modules (`4.47M` LOC), **31,820** unused `def`/`structure` modules (`4.98M` LOC), **24,899** unused bookkeeping helper modules (`2.12M` LOC), **1,946** `instance`/`class` modules (`426k` LOC, which together with their 2,142 prerequisite modules are automatically retained by `materialize --mode instance-aware`), and **174** zero-declaration barrel modules.

### Sample Outputs (`examples/rh_alpo/`)

- [paper.pdf](examples/rh_alpo/paper.pdf) — Compiled 36-page Annals-style PDF manuscript (227 KB, compiled via `tectonic` with zero TeX errors).
- [paper.tex](examples/rh_alpo/paper.tex) — LaTeX manuscript source (12 topological chapters / 96 sections, 769 unique `\leanlink` anchors).
- [blueprint.html](examples/rh_alpo/blueprint.html) — Interactive 3-zoom-level proof DAG, KaTeX chapter explorer, and Lean declaration inspector (427 KB).
- [audit_report.md](examples/rh_alpo/audit_report.md) / [audit_report.json](examples/rh_alpo/audit_report.json) — Automated statement/dependency audit (`PASS`, fidelity `1.0000`, 0 issues).
- [optimization_report.md](examples/rh_alpo/optimization_report.md) — Quantitative 8-stage compression ladder, module-import vs declaration-reachability breakdown, package-by-package deduplication audit, and system optimization roadmap.
- [refactor_plan.md](examples/rh_alpo/refactor_plan.md) — Top 20 ranked Stage 4 refactoring work orders.
