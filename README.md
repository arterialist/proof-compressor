# proof-compressor

Compress, analyze, audit, materialize, and expose massive Lean 4 proof repositories into human-readable mathematics, interactive proof blueprints, compilable merged/pruned Lean projects, and kernel-checked refactoring plans.

## System Overview (5 Stages)

1. **Lean 4 `.olean` Kernel Extractor (`lean_extractor/`, `proof_compressor.ingest.olean_bridge`)**
   - Self-contained Lean 4 metaprogram (`ExtractDag.lean`) that loads a compiled `Environment`, walks `Expr.getUsedConstants` from target roots stopping at Mathlib/Init/Std/Lean boundaries, collects kernel proof-term sizes and `#print axioms` footprints, and emits JSONL directly into SQLite.
2. **Zero-Extraction Streaming Source Ingestor (`proof_compressor.ingest`, `proof_compressor.schema`)**
   - Streams `.lean` sources straight from directories, `.tar.gz`, or multi-part `.tar.gz.part01..N` archives directly into a WAL-tuned SQLite dependency graph with zero disk extraction, two-pass transitive import resolution, alpha-equivalent `canonical_type_hash`, and bookkeeping heuristics.
3. **Graph Pruning, Compilable Multi-Pass Materialization & Merging, Deduplication, Topology & Clustering (`proof_compressor.analyze`)**
   - **Reachability pruning (`prune.py`)**: Exact reverse-dependency traversal from explicit or auto-detected `Main`/`Statements` roots with Mathlib boundary isolation.
   - **Multi-pass Lean 4 compression & module merging (`materialize.py`, `consolidate.py`, `merge_modules.py`)**: Stream-materializes a pruned, import-rewritten, duplicate-consolidated, module-merged Lean 4 project directly to a directory or `.tar.gz` (`--output-archive`) with zero intermediate disk unpacking:
     - `instance-aware` *(compilable default)*: keeps declaration-reachable modules plus any transitively imported `instance`/`class`/syntax/bridge support modules, rewrites `import` headers to eliminate dead side-imports, and strips unreferenced intra-module theorems/lemmas.
     - `--collapse-barrels`: eliminates pure forwarding zero-declaration barrel modules by splicing their live imports into callers.
     - `--consolidate-duplicates`: delegates source-verified exact-duplicate proofs to canonical `_root_.` calls (both pre-merge in-scope and Phase-B cross-branch post-merge).
     - `--strip-comments`: strips comments and consecutive blank lines safely (preserving string literals and balanced nested `/- ... -/` blocks).
     - `--merge-modules` (`--target-module-loc`): fuses single-consumer linear chains and bundles same-`(lean_lib_root, layer)` antichains into section-isolated bundles (`section __pc_u_* ... end __pc_u_*`), eliminating redundant `import` headers while keeping macro/syntax/root modules standalone and preserving an acyclic module DAG.
   - **Deduplication (`dedup.py`)**: Exact `canonical_type_hash` groups, alpha/namespace-normalized near-duplicates, isomorphic definitions, and Mathlib-absorption candidates.
   - **Scalable topology (`topology.py`)**: Pure-stdlib CSR graphs with iterative Tarjan SCC, iterative Cooper–Harvey–Kennedy dominator trees, exact/landmark-sketch DAG flow, bottleneck scoring, and transitively reduced pillar backbones (500k nodes / 2M edges in ~4.5s).
   - **Modular clustering (`cluster.py`)**: Hierarchical chapter/section DAG clustering with exact `Inputs ⊢ Outputs` interfaces.
4. **Mathematical Exposition & Fidelity Auditing (`proof_compressor.expose`)**
   - **Symbol registry & filtering (`symbols.py`, `filter.py`)**: Maps high-centrality Lean declarations to consistent standard mathematical notation, collapses Lean bookkeeping glue, and tags cluster proof idioms.
   - **Annals-style LaTeX, Manuscript Assembly & Compiled PDFs (`latex.py`, `manuscript.py`)**: Deterministic synthesis of `paper.tex` plus modular Annals-style `manuscript.tex` / `manuscript.pdf` assembly (35-page compiled human-readable monograph with zero TeX errors via `tectonic`), complete with `\leanlink{...}` anchors and an optional guarded LLM refinement hook.
   - **Interactive 3-Zoom Blueprint (`blueprint.html` via `blueprint.py`)**: Self-contained zero-build HTML proof map (Level 0 bottleneck/chapter DAG, Level 1 KaTeX chapters with formal interfaces, Level 2 Lean declaration & dependency inspector).
   - **Automated Auditor (`audit.py`)**: Verifies every `\leanlink` exists and is reachable, checks all prose proof citations lie in the Lean dependency DAG, detects omitted high-bottleneck dependencies, dropped hypotheses, symbol drift, and Lean bookkeeping leaks.
5. **Kernel-Checked Refactoring & Proof Simplification Engine (`proof_compressor.refactor`)**
   - **Planner (`planner.py`)**: Ranks high-leverage refactoring targets by internal LOC, interface narrowness, duplication, and Mathlib-absorption potential, emitting self-contained `Inputs ⊢ Outputs` work orders.
   - **Live Proof Simplifier (`simplify.py`)**: Transactional Stage 4 source rewrites (dead `have`/`let`/`set`/private helper pruning, `first | ...` / `by exact` / `have; simpa` collapse, consecutive `rw` merging, tactical automation lifting, and Mathlib delegation) guarded by `verify_refactor_gate`.
   - **Verification gate (`gate.py`)**: Enforces `lake build`, `#print axioms` invariance, `#check @decl` exported signature preservation, and strict LOC reduction (with automatic rollback on failure).

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

# Stream-emit a compilable, barrel-collapsed, duplicate-consolidated, merged Lean 4 archive
uv run proof-compressor materialize outputs/proof.db \
  --source data/lean.tar.gz.part01 \
  --output-archive outputs/rh_merged.tar.gz \
  --mode instance-aware \
  --collapse-barrels \
  --consolidate-duplicates \
  --strip-comments \
  --merge-modules \
  --target-module-loc 1400

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

End-to-end zero-extraction run over the complete 14-part `alpo.ge` Lean 4 formalization (`lean.tar.gz.part01..part14`, 239.28 MB compressed / 1.031 GB uncompressed, auto-detecting all 5 root theorems in `Main.lean`: `riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`):

### Multi-Pass Archive Compression & Module Merging Waterfall

| Compression Stage | Modules | Module Reduction | Non-Blank LOC | Uncompressed Size | `.tar.gz` Archive |
|---|---:|---:|---:|---:|---:|
| **Raw `alpo.ge` Archive (`part01..14`)** | 175,187 | 0.00% | 15,531,759 | 1,030.54 MB (`1.031 GB`) | 239.28 MB |
| **Strict `import-closure` Pruning** | 175,184 | -0.002% | 15,531,434 | ~1,030.5 MB | — |
| **Converged `instance-aware` + Rescue + Barrel Collapse + Dedup + Strip (`rh_compressed.tar.gz`)** | 149,106 | -14.89% | 13,126,611 (`-15.49%`) | 869.29 MB (`-15.65%`) | 202.48 MB (`-15.38%`) |
| **`--merge-modules` + Phase-B Consolidation (`rh_merged.tar.gz`)** | **3,188** | **-98.18% (`55.0x`)** | **12,792,153** (`-17.64%`) | **814.09 MB** (`-21.00%`) | **184.46 MB** (`-22.91%`) |
| **`decl-exact` Reachable Core (Analytical / DB)** | 35,669 | -79.64% | 2,895,538 (`-81.36%` stripped) | — | — |

Key measured highlights (`outputs/rh_merged.tar.gz` with `--target-module-loc 5500`, emitted in `917.34s` with zero intermediate disk unpacking, `0` import cycles, `0` dangling imports, `0` zero-import files, `0` `sorry`/`admit`):
- **Module fusion**: `175,187 -> 149,106 -> 3,188` modules (`-98.18%` / `55.0x` vs raw), eliminating **605,773** redundant `import` lines (`-334,458` net merge LOC) and collapsing **149** pure forwarding barrels while retaining `def`/`structure`, `_root_.`, Greek-prefix `anon_*`, dot-projection, `instance`/`class`, and `Mathlib` transitive import closures required for Lean `v4.33.1` compilation.
- **Dead-lemma stripping & exact-duplicate consolidation**: Stripped **55,835** dead intra-module theorems/lemmas (`-689,395` LOC) and consolidated **10,214** source-verified exact-duplicate proofs (`-81,649` LOC: `1,458` pre-merge + `8,756` Phase-B post-merge).
- **Declarations & deduplication potential**: `1,061,425` raw -> `183,501` reachable declarations (`-82.71%`; `7,541,179 -> 955,634` edges) and `2,252,399 -> 1,597,336` est. post-dedup body LOC (`-29.08%` further; `~9.72x` cumulative from raw LOC).

### Real Lean `v4.33.1` + Mathlib Verification & Stage 4 Proof Simplification

- **Full-corpus soundness audit**: Streaming scan across all **175,187 `.lean` files (15,531,759 lines)** verified **0 `sorry`**, **0 `admit`**, **0 custom `axiom`**, **0 `opaque`**, **0 `constant`**, **0 `unsafe`**, and **0 `native_decide`** declarations.
- **Live Lean `v4.33.1` + Mathlib (`0df444a360ea`) kernel verification**: Verified 6 real compressed RH modules (`BuildAid.D1..D5`, `CurveKrullDimTopology`, `ExtendOneMulVecSingleLast`, and 4 `Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.*` modules) with `lake build` + `#check @decl` + `#print axioms` (**63/63** non-primed exported declarations + `C2'` baseline verified in `{propext, Classical.choice, Quot.sound}`).
- **Live Stage 4 proof simplification (`simplify.py`)**: Kernel-verified simplifications across the 4 `SharpRestriction` modules reduced effective LOC **`646 -> 613` (`-5.1%`)** and proof steps **`507 -> 478` (`-5.7%`)**, while exposing the `anon_*` (`τk_*`) and dot-projection (`PhiData.*`) rescue rules subsequently fixed and verified in `materialize.py` (`49/49` `pytest` tests passing). See [simplification_results.md](examples/rh_alpo/simplification_results.md).
- **Why `Main.lean`'s raw `import` closure pulled in 175,184 of 175,187 modules**:
  1. **Umbrella barrel side-imports**: `Supplements.Kernels.MainTheoremsAll` and `MainTheoremsCritical` define zero declarations of their own, yet import 4 unused `SmallClassNumbers.*` modules (`CorGKOf` alone transitively pulls in **170,699 modules** via module imports even though `Main.lean` never references `CorGKOf`).
  2. **Over-wide file import headers**: The 35,669 declaration-reachable modules contain **10,255 unused `import` lines** that were only needed by dead intra-module declarations.
  3. **Breakdown of the 139,515 imported-but-unreached modules (`11,996,775` LOC)**: **80,676** pure unused theorem/lemma modules (`4.47M` LOC), **31,820** unused `def`/`structure` modules (`4.98M` LOC), **24,899** unused bookkeeping helper modules (`2.12M` LOC), **1,946** `instance`/`class` modules (`426k` LOC), and **174** zero-declaration barrel/tactic modules.

### Sample Outputs (`examples/rh_alpo/`)

- [readers_guide.pdf](examples/rh_alpo/readers_guide.pdf) / [readers_guide.tex](examples/rh_alpo/readers_guide.tex) — **6-page** standalone Big-Picture Conceptual Reader's Guide with TikZ proof-architecture diagram, plain-math exposition of the iterated theta-lift / $2/3$-barrier resolution, 10-row quantitative closure table, and Reading Map (`PASS`, fidelity **`1.0000`**, **39** unique / **55** total verified `\leanlink` anchors in [readers_guide_audit.md](examples/rh_alpo/readers_guide_audit.md)).
- [manuscript.pdf](examples/rh_alpo/manuscript.pdf) / [manuscript.tex](examples/rh_alpo/manuscript.tex) — **35-page** human-readable Annals-style mathematical monograph synthesized across 5 curated chapters ([chapters/](examples/rh_alpo/chapters/)), audited against `outputs/rh_full.db` (`PASS`, fidelity **`1.0000`**, **360** unique / **597** total verified `\leanlink` anchors, **0** issues across all 7 checks in [manuscript_audit.md](examples/rh_alpo/manuscript_audit.md)).
- [paper.pdf](examples/rh_alpo/paper.pdf) / [paper.tex](examples/rh_alpo/paper.tex) — Compiled 36-page deterministic cluster-driven PDF manuscript (`1.0000` audit fidelity across **769** unique / **1,128** total verified `\leanlink` anchors).
- [blueprint.html](examples/rh_alpo/blueprint.html) — Upgraded interactive 3-zoom-level proof map featuring the 5-chapter proof architecture DAG, direct links to `readers_guide.pdf` and `manuscript.pdf`, KaTeX chapter explorer, and Level 2 Lean declaration inspector (508 inspectable declarations).
- [simplification_results.md](examples/rh_alpo/simplification_results.md) — Live Stage 4 Lean `v4.33.1` + Mathlib kernel-checked simplification diffs, `#print axioms` verification, and top-3 structural detour roadmap.
- [optimization_report.md](examples/rh_alpo/optimization_report.md) — Quantitative 8-stage compression waterfall, module-import vs declaration-reachability breakdown, package-by-package deduplication audit, and system optimization roadmap.
- [audit_report.md](examples/rh_alpo/audit_report.md) / [audit_report.json](examples/rh_alpo/audit_report.json) — Automated statement/dependency audit (`PASS`, fidelity `1.0000`, 0 issues).
- [refactor_plan.md](examples/rh_alpo/refactor_plan.md) — Top 20 ranked Stage 4 refactoring work orders.
