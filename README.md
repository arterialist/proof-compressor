# proof-compressor

Compress, analyze, audit, materialize, and expose massive Lean 4 proof repositories into human-readable mathematics, interactive proof blueprints, pruned and merged Lean projects, and kernel-checked refactoring plans.

## System Overview (5 Stages)

1. **Lean 4 `.olean` Kernel Extractor (`lean_extractor/`, `proof_compressor.ingest.olean_bridge`)**
   - Self-contained Lean 4 metaprogram (`ExtractDag.lean`) that loads a compiled `Environment`, walks `Expr.getUsedConstants` from target roots stopping at Mathlib/Init/Std/Lean boundaries, collects kernel proof-term sizes and `#print axioms` footprints, and emits JSONL directly into SQLite.
2. **Zero-Extraction Streaming Source Ingestor (`proof_compressor.ingest`, `proof_compressor.schema`)**
   - Streams `.lean` sources straight from directories, `.tar.gz`, or multi-part `.tar.gz.part01..N` archives directly into a WAL-tuned SQLite dependency graph with zero disk extraction, two-pass transitive import resolution, alpha-equivalent `canonical_type_hash`, and bookkeeping heuristics.
3. **Graph Pruning, Multi-Pass Materialization & Merging, Deduplication, Topology & Clustering (`proof_compressor.analyze`)**
   - **Reachability pruning (`prune.py`)**: Exact reverse-dependency traversal from explicit or auto-detected `Main`/`Statements` roots with Mathlib boundary isolation.
   - **Multi-pass Lean 4 compression & module merging (`materialize.py`, `consolidate.py`, `merge_modules.py`)**: Stream-materializes a pruned, import-rewritten, duplicate-consolidated, module-merged Lean 4 project directly to a directory or `.tar.gz` (`--output-archive`) with zero intermediate disk unpacking:
     - `instance-aware` *(default)*: keeps declaration-reachable modules plus any transitively imported `instance`/`class`/syntax/bridge support modules, rewrites `import` headers to eliminate dead side-imports, and strips unreferenced intra-module theorems/lemmas.
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
uv run proof-compressor audit --db outputs/proof.db --latex outputs/exposition/paper.tex
uv run proof-compressor refactor-plan --db outputs/proof.db --out-md outputs/exposition/refactor_plan.md

# Stream-emit a barrel-collapsed, duplicate-consolidated, merged Lean 4 archive
uv run proof-compressor materialize outputs/proof.db \
  --source data/lean.tar.gz.part01 \
  --output-archive outputs/rh_merged.tar.gz \
  --mode instance-aware \
  --collapse-barrels \
  --consolidate-duplicates \
  --strip-comments \
  --merge-modules \
  --target-module-loc 1400 \
  --external-names mathlib_names.txt   # optional: every Mathlib constant name, one per line; enables name-capture repair

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
| **Raw `alpo.ge` Archive (`part01..14`)** | 175,187 | 0.00% | 15,531,759 | 1,030.54 MB | 239.28 MB |
| **Strict `import-closure` Pruning** | 175,184 | -0.00% | 15,531,434 | — | — |
| **Declaration-Reachable Cone (Analytical / DB)** | 145,276 | -17.07% | 13,427,197 (10,432,497 decl-body LOC) | — | — |
| **`instance-aware` + Barrel Collapse + Dedup + Strip (`rh_compressed.tar.gz`)** | 149,208 | -14.83% | 13,128,024 (`-15.48%`) | 868.41 MB | 202.29 MB (`-15.46%`) |
| **`--merge-modules` + Phase-B Consolidation (`rh_merged.tar.gz`)** | **4,685** | **-97.33% (`37.4x`)** | **12,812,699** (`-17.51%`) | **815.09 MB** | **184.92 MB** (`-22.72%`) |

Measured on `outputs/rh_merged.tar.gz` (`--target-module-loc 5500`, 1218s, streamed with no extraction to disk; `0` import cycles, `0` dangling imports):
- **Module fusion**: `175,187 -> 149,208 -> 4,685` modules, removing **587,150** `import` lines (`-315,325` net LOC) and collapsing **150** pure forwarding barrels.
- **Dead-lemma stripping & exact-duplicate consolidation**: stripped **57,079** unreferenced intra-module theorems/lemmas (`-719,449` LOC) and delegated **9,963** source-verified exact-duplicate proofs (`-79,650` LOC: `1,461` pre-merge + `8,502` Phase-B post-merge).
- **Declarations & deduplication potential**: `1,061,531` raw -> `799,064` reachable declarations (`-24.73%`), and `10,432,497 -> 7,302,799` estimated post-dedup body LOC (`-30.0%`).

> **Reachability numbers changed substantially in this revision.** The source parser previously dropped references through Unicode identifiers (`hσ`, `Gammaℝ`), `_root_.`-qualified names, Greek-initial declaration names, `alias` declarations, field notation on locals and `variable` binder types, and produced false edges from proof-local names. The declaration-reachable cone is now 145,276 modules / 799,064 declarations (previously reported as 35,669 / 183,501). The pruned archives changed little, because instance-aware materialization was already keeping those modules.

### Real Lean `v4.33.1` + Mathlib Verification & Stage 4 Proof Simplification

- **Full-corpus soundness audit**: Streaming scan across all **175,187 `.lean` files (15,531,759 lines)** verified **0 `sorry`**, **0 `admit`**, **0 custom `axiom`**, **0 `opaque`**, **0 `constant`**, **0 `unsafe`**, and **0 `native_decide`** declarations.
- **Compile status of the merged archive**: not yet built in full. A targeted `lake build` (Lean `v4.33.1` + Mathlib `0df444a360ea`) of the 21 bundles that hold every declaration that failed in earlier archives, plus their import closure (76 of 4,685 modules), finishes with **0 errors**. `Main` has not been compiled from the merged archive, so `#print axioms` on the root theorems is still open. See [optimization_report.md](examples/rh_alpo/optimization_report.md) §4 for what was checked and the known residual risk.
- **Live Lean `v4.33.1` + Mathlib (`0df444a360ea`) kernel verification**: Verified 6 real compressed RH modules (`BuildAid.D1..D5`, `CurveKrullDimTopology`, `ExtendOneMulVecSingleLast`, and 4 `Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.*` modules) with `lake build` + `#check @decl` + `#print axioms` (**63/63** non-primed exported declarations + `C2'` baseline verified in `{propext, Classical.choice, Quot.sound}`).
- **Live Stage 4 proof simplification (`simplify.py`)**: Kernel-verified simplifications across the 4 `SharpRestriction` modules reduced effective LOC **`646 -> 613` (`-5.1%`)** and proof steps **`507 -> 478` (`-5.7%`)**. See [simplification_results.md](examples/rh_alpo/simplification_results.md).
- **Why `Main.lean`'s raw `import` closure pulls in 175,184 of 175,187 modules while only 145,276 are declaration-reachable**:
  1. **Umbrella barrel side-imports**: `Supplements.Kernels.MainTheoremsAll` and `MainTheoremsCritical` define no declarations of their own, yet import 4 `SmallClassNumbers.*` modules that no reachable declaration references.
  2. **Imported-but-unreferenced modules**: 29,911 modules (2,104,562 LOC): 18,066 theorem/lemma-only modules, 7,023 `def`/`structure` modules, 4,130 bookkeeping helper modules, 518 `instance`/`class` modules (kept for typeclass synthesis), and 174 zero-declaration barrel/tactic modules.

### Sample Outputs (`examples/rh_alpo/`)

- [readers_guide.pdf](examples/rh_alpo/readers_guide.pdf) / [readers_guide.tex](examples/rh_alpo/readers_guide.tex) — **6-page** standalone Big-Picture Conceptual Reader's Guide with TikZ proof-architecture diagram, plain-math exposition of the iterated theta-lift / $2/3$-barrier resolution, 10-row quantitative closure table, and Reading Map (`PASS`, fidelity **`1.0000`**, **38** unique / **54** total verified `\leanlink` anchors in [readers_guide_audit.md](examples/rh_alpo/readers_guide_audit.md)).
- [manuscript.pdf](examples/rh_alpo/manuscript.pdf) / [manuscript.tex](examples/rh_alpo/manuscript.tex) — **35-page** human-readable Annals-style mathematical monograph synthesized across 5 curated chapters ([chapters/](examples/rh_alpo/chapters/)), audited against `outputs/rh_full.db` (`PASS`, fidelity **`1.0000`**, **360** unique / **597** total verified `\leanlink` anchors, **0** issues across all 7 checks in [manuscript_audit.md](examples/rh_alpo/manuscript_audit.md)).
- [paper.pdf](examples/rh_alpo/paper.pdf) / [paper.tex](examples/rh_alpo/paper.tex) — Compiled 38-page deterministic cluster-driven PDF manuscript (`1.0000` audit fidelity across **849** unique / **1,198** total verified `\leanlink` anchors).
- [blueprint.html](examples/rh_alpo/blueprint.html) — Upgraded interactive 3-zoom-level proof map featuring the 5-chapter proof architecture DAG, direct links to `readers_guide.pdf` and `manuscript.pdf`, KaTeX chapter explorer, and Level 2 Lean declaration inspector (552 inspectable declarations).
- [simplification_results.md](examples/rh_alpo/simplification_results.md) — Live Stage 4 Lean `v4.33.1` + Mathlib kernel-checked simplification diffs, `#print axioms` verification, and top-3 structural detour roadmap.
- [optimization_report.md](examples/rh_alpo/optimization_report.md) — Measured compression waterfall, module-import vs declaration-reachability breakdown, Lean compile-check status, and package-by-package duplication tables.
- [audit_report.md](examples/rh_alpo/audit_report.md) / [audit_report.json](examples/rh_alpo/audit_report.json) — Automated statement/dependency audit (`PASS`, fidelity `1.0000`, 0 issues).
- [refactor_plan.md](examples/rh_alpo/refactor_plan.md) — Top 20 ranked Stage 4 refactoring work orders.
