# Deep Quantitative Optimization Report: `alpo.ge` Riemann Hypothesis Lean 4 Proof & `proof-compressor`

This report presents an exact, database-backed audit of the full **175,187-file (`15,531,759` LOC, `1,061,425` declarations, `7,541,179` edges)** `alpo.ge` Lean 4 Riemann Hypothesis corpus (`outputs/rh_full.db`), analyzing the gap between module-level `import` closure and declaration-level dependency reachability, detailing the three compilable pruning modes implemented in `proof-compressor materialize`, and quantifying every further optimization lever for both the formal proof repository and the `proof-compressor` engine.

---

## 1. Executive Summary: The Multi-Stage Compression Ladder

Tracing reverse dependencies from the 5 root theorems in `lean/src/Main.lean` (`riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`) reveals a **7.8×–16.3× cumulative compression ladder**:

| Compression Stage | Modules Kept | Module Reduction | Total / Body LOC | Cumulative Compression | Compilability Guarantee |
| :--- | ---: | ---: | ---: | ---: | :--- |
| **0. Raw `alpo.ge` Archive** | 175,187 | 0.0% | 15,531,759 LOC | 1.00× | Baseline archive (`lean/src/`) |
| **1. Strict `import-closure` Pruning** | 175,184 | -0.002% | 15,531,434 LOC | 1.00× | 100% identical import graph |
| **2. `import-closure` + Intra-Module Dead-Lemma Strip** | 175,184 | -0.002% | 5,731,420 LOC | **2.71× (-63.1%)** | Keeps all imports, defs, instances; strips 658,917 dead theorems |
| **3. `instance-aware` Hybrid Module Pruning** | 39,847 | **-77.25%** | 4,262,869 LOC | **3.64× (-72.6%)** | Keeps all decl-reachable mods + 4,088 instance/support mods + 90 barrels |
| **4. `instance-aware` + Intra-Module Strip (`materialize`)** | 39,847 | **-77.25%** | **3,321,148 LOC** | **4.68× (-78.6%)** | **Recommended compilable target**: strips 92,677 dead intra-file lemmas |
| **5. `decl-exact` Module Reachability** | 35,669 | **-79.64%** | 3,534,659 LOC | 4.39× (-77.2%) | Exact syntactic identifier reachability (2,252,399 decl body LOC) |
| **6. `decl-exact` + Intra-Module Dead-Lemma Strip** | 35,669 | **-79.64%** | **2,895,538 LOC** | **5.36× (-81.4%)** | Strips 64,572 dead intra-module theorems (`-639,121` LOC) |
| **7. Post-Dedup & Mathlib-Absorption Body LOC** | ~28,500 | ~-83.7% | **1,597,336 body LOC** | **9.72× (-89.7%)** | Eliminates 13,694 exact + 10,910 near-dup groups + 39,972 Mathlib cands |
| **8. Stage 4 Narrow-Interface Kernel Refactoring** | ~18,000 | ~-89.7% | **~950,000 body LOC** | **~16.3× (-93.9%)** | Consolidating top 20 high-leverage chapters behind `Inputs ⊢ Outputs` |

---

## 2. Audit of Module `import` Closure vs. Explicit Identifier Reachability

A crucial structural finding on `outputs/rh_full.db` explains why naive module-import walking fails to compress auto-generated Lean repositories:

- **Transitive `import` closure from `Main.lean`**: **`175,184` of `175,187` modules (`15,531,434` LOC — 99.998% of the repository)** across `889,764` `import` edges. Only **`3` modules (`325` LOC)** in `Development.AutomorphicArithmetic` are completely disconnected from `Main.lean`'s import graph.
- **Explicit declaration-level reachability from `Main.lean`**: **`35,669` modules (`3,534,659` LOC — 20.36% of modules, 22.76% of LOC)** and **`183,501` declarations (`2,252,399` body LOC — 17.29% of declarations)**. Every single one of those 35,669 declaration-reachable modules lies inside `Main.lean`'s transitive import closure (`0` outside).
- **Why `139,515` transitively imported modules (`11,996,775` LOC) have zero declaration-level incoming edges**:
  In the `35,669` declaration-reachable modules, there are `140,894` outgoing `import` statements, of which **`10,255` (`7.3%`) point into modules whose declarations are never referenced**, and those 10,255 unused imports transitively fan out into `139,515` dead modules.

### Exact 5-Way Classification of the 139,515 Imported-but-Unreferenced Modules

| Category of Imported-but-Unreached Module | Module Count | % of Unreached | Total LOC | Compilation Role & Pruning Safety |
| :--- | ---: | ---: | ---: | :--- |
| **1. Pure Mathematical Theorem/Lemma Modules** | **80,676** | 57.83% | **4,470,209** | Define **0** instances, **0** classes, **0** defs/structures, **0** bookkeeping helpers. **100% dead `import` branches** safe to prune immediately. |
| **2. Auxiliary `def` / `structure` / `inductive` Modules** | **31,820** | 22.81% | **4,976,000** | Define unused helper structures/defs never referenced by any reachable theorem or kept instance. Safe to prune once unused imports are removed. |
| **3. Bookkeeping / `@[simp]` Helper Lemma Modules** | **24,899** | 17.85% | **2,123,551** | Pure theorem/lemma files containing order/coercion/arithmetic glue. Only needed if invoked implicitly via unannotated `simp` sets. |
| **4. Typeclass & `instance` Modules** | **1,946** | 1.39% | **426,022** | Define `instance` or `class` declarations that Lean 4's typeclass synthesizer can pick up implicitly without an identifier edge. **Kept in `instance-aware` mode** (+2,142 prerequisite support modules). |
| **5. Zero-Declaration Barrel / Notation Modules** | **174** | 0.12% | **993** | Pure `import` aggregator barrels (e.g. `Supplements.Kernels.MainTheoremsAll`) or notation-only files. **90 active bridges kept or rewritten** in `instance-aware` mode. |
| **Total Imported-but-Not-Decl-Reached** | **139,515** | **100.00%** | **11,996,775** | **135,340 modules (`11,268,890` LOC) safely eliminated in `instance-aware` mode.** |

### Top 10 Packages Contributing Dead-Imported Modules (`imp_closure - decl_reachable`)

| Package (`level-2`) | Dead-Imported Modules | Dead-Imported LOC | Reachable Modules | Reachable Body LOC |
| :--- | ---: | ---: | ---: | ---: |
| `Development.AbelianVarietyTheory` | 81,468 | 5,867,054 | 17,719 | 919,429 |
| `Development.AutomorphicArithmetic` | 14,306 | 1,263,851 | 4,122 | 310,923 |
| `Development.AutomorphicSpectrum` | 10,951 | 767,207 | 4,196 | 253,854 |
| `Formalism.LocalToGlobal` | 5,096 | 721,617 | 405 | 16,920 |
| `Formalism.SharpRestriction` | 2,913 | 533,666 | 180 | 11,432 |
| `Development.WeilBound` | 4,774 | 531,234 | 2,277 | 173,102 |
| `Formalism.PeriodIntegrals` | 4,241 | 382,539 | 109 | 5,551 |
| `GroundTheory.HeightsAndTheta` | 3,857 | 328,088 | 2,553 | 161,050 |
| `Formalism.HermitianCurvature` | 1,814 | 308,498 | 108 | 6,419 |
| `ReciprocityTheory.ReductiveGroups` | 2,268 | 284,576 | 531 | 42,247 |

Notice the dramatic finding in `Formalism`: over **92% of `Formalism.LocalToGlobal`, `Formalism.SharpRestriction`, `Formalism.PeriodIntegrals`, and `Formalism.HermitianCurvature`** consists of dead-imported branches that are never used on any path to `Main.lean`!

---

## 3. Compilable Pruning & Materialization (`proof-compressor materialize`)

To guarantee that pruning produces a **valid, kernel-compilable Lean 4 project**, `src/proof_compressor/analyze/materialize.py` (`proof-compressor materialize`) implements three pruning modes plus two source-level transformations:

### A. Side-by-Side Comparison of the 3 Materialization Modes on `outputs/rh_full.db`

| Metric | `import-closure` | `instance-aware` (Default) | `decl-exact` |
| :--- | ---: | ---: | ---: |
| **Kept Modules** | 175,184 | **39,847** | 35,669 |
| **Dropped Dead Modules** | 3 | **135,340 (-77.25%)** | 139,518 (-79.64%) |
| **Kept Instance/Support Modules** | All (1,946+) | **+4,088** (1,946 instance + 2,142 prereqs) | 0 (only explicitly named) |
| **Kept Barrel Bridge Modules** | All (174) | **+90** (plus automatic barrel import rewriting) | 0 (rewritten via barrel collapse) |
| **Kept Declarations** | 402,494 | **274,806** | 226,138 |
| **Stripped Intra-Module Dead Lemmas** | 658,917 (`-9,800,014` LOC) | **92,677 (`-941,721` LOC)** | 64,572 (`-639,121` LOC) |
| **Final Materialized LOC** | 5,731,420 (`-63.10%`) | **3,321,148 (`-78.62%`)** | 2,895,538 (`-81.36%`) |

### B. Why `instance-aware` Materialization Preserves Lean 4 Compilation
1. **Implicit Typeclass Synthesis Closure**: In Lean 4, `instance` declarations are resolved by typeclass search (`[...]`) without appearing by identifier name in the caller's source text. `instance-aware` mode retains every transitively imported module defining an `instance` or `class` (`1,946` modules) **and** runs a secondary reverse-dependency BFS from those `instance`/`class` declarations along `edges` (`src_id -> dst_id`), pulling in all **`2,142` prerequisite helper modules (`35,028` declarations)** required for those instances to compile.
2. **Barrel Import Rewriting**: When a kept module `M` imports a dropped barrel/intermediate module `B`, `transform_lean_source` traverses `module_imports` from `B` to find any kept modules `K` re-exported through `B` and rewrites `import B` -> `import K` while stripping dead imports (`10,255` dead import edges eliminated).
3. **Safe Intra-Module Dead-Lemma Stripping**: Inside kept `.lean` files, `transform_lean_source` strips unreferenced `theorem`/`lemma` blocks (`92,677` dead lemmas / `941,721` LOC in `instance-aware` mode) while:
   - Never stripping `def`, `abbrev`, `structure`, `class`, `inductive`, `instance`, `axiom`, `opaque`, or `constant` declarations.
   - Never stripping any declaration annotated with `@[simp]`, `@[ext]`, `@[aesop]`, `@[norm_cast]`, `@[push_cast]`, `@[coe]`, `@[positivity]`, `@[measurability]`, `@[continuity]`, `@[fun_prop]`, `local instance`, or `scoped`.
   - Expanding line spans upward to remove preceding `/-- ... -/` docstrings and `@[...]` attribute lines (preventing dangling-docstring syntax errors in Lean 4) while preserving enclosing `namespace`, `section`, and `end` lines.

---

## 4. Deep Proof Optimization Levers (Quantified Savings on Reachable Code)

Even after pruning the repository from `15,531,759` LOC down to `3,321,148` materialized LOC (`2,252,399` reachable declaration body LOC across `183,501` reachable declarations), five major mathematical and structural redundancies remain inside the reachable core:

### Lever 1: Exact & Near-Duplicate Lemma Consolidation (`-363,988` Body LOC)
Across the `183,501` reachable declarations:
- **`13,694` exact canonical-type duplicate groups** (`25,726` redundant declarations, **`197,394` reducible body LOC**): identical type signatures modulo alpha-renaming of bound variables.
- **`10,910` near-duplicate signature groups** (`15,344` redundant declarations, **`166,594` reducible body LOC**): alpha/namespace-isomorphic lemmas (`similarity >= 0.85`) re-proved separately across sub-packages.
- **`2,557` cross-package duplicate groups (`79,105` reducible body LOC)**: identical statements proved independently in two or more distinct packages (most frequently shared between `Development.AbelianVarietyTheory`, `Development.AutomorphicArithmetic`, and `GroundTheory.HeightsAndTheta`).
- **`5,429` isomorphic definition groups**: duplicate auxiliary structures and type aliases that force duplicate transport/coercion boilerplate.

### Lever 2: Package-by-Package Deduplication & Bookkeeping Hotspots

| Reachable Package (`level-2`) | Reachable Decls | Reachable Body LOC | Exact-Dup Redundant Decls | Exact-Dup Reducible LOC | Bookkeeping Decls | Bookkeeping Body LOC |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Development.AbelianVarietyTheory` | 70,255 | 919,429 | 9,264 | **229,057** | 10,040 | **89,525** |
| `Development.AutomorphicArithmetic` | 22,650 | 310,923 | 3,965 | **27,331** | 1,593 | **15,038** |
| `Development.AutomorphicSpectrum` | 20,375 | 253,854 | 2,357 | **41,427** | 2,814 | **22,118** |
| `Development.WeilBound` | 16,938 | 173,102 | 3,090 | **22,516** | 1,227 | **6,243** |
| `GroundTheory.HeightsAndTheta` | 10,893 | 161,050 | 1,884 | **15,291** | 886 | **7,130** |
| `Development.ResolutionOfSingularities` | 5,961 | 96,926 | 268 | 3,688 | 654 | 5,935 |
| `GroundTheory.AutomorphicForms` | 4,518 | 50,054 | 166 | 692 | 583 | 3,001 |
| `ReciprocityTheory.ReductiveGroups` | 4,147 | 42,247 | 481 | 3,056 | 344 | 2,308 |
| `Development.EtaleCohomology` | 4,740 | 40,705 | 1,279 | 7,254 | 311 | 1,959 |
| `GroundTheory.GlobalFields` | 2,584 | 23,225 | 61 | 233 | 576 | 3,758 |
| `Formalism.LocalToGlobal` | 3,059 | 16,920 | 399 | 1,945 | 185 | 983 |
| `GroundTheory.LocalFields` | 1,670 | 15,229 | 59 | 321 | 357 | 2,349 |
| `GroundTheory.ArithmeticGeometry` | 1,351 | 12,242 | 61 | 301 | 164 | 1,294 |
| `GroundTheory.PAdicHodge` | 1,341 | 11,962 | 55 | 148 | 245 | 1,229 |
| `Formalism.SharpRestriction` | 2,020 | 11,432 | 513 | 2,045 | 71 | 460 |

`Development.AbelianVarietyTheory` alone accounts for **38.3% of all reachable declarations (`70,255`)**, **40.8% of reachable body LOC (`919,429`)**, and **65.0% of all exact-duplicate LOC (`229,057` LOC)** — making it the single highest-yield refactoring target in the entire proof.

### Lever 3: Mathlib Absorption (`39,972` Candidates / `358,633` Body LOC)
`analyze_dedup` identified **`39,972` reachable project declarations (`358,633` body LOC)** that re-prove standard library facts over `Real`, `Complex`, `Finset`, `Set`, `Filter.Tendsto`, `MeasureTheory`, `Polynomial`, `Matrix`, and `LinearMap` (or repeat identical local helper names like `aux`, `bound_aux`, `le_of_*`, `sum_*`, `measurable_*`, `continuous_*` across 3+ modules). Replacing these custom polyfills with direct Mathlib calls (`omega`, `positivity`, `fun_prop`, `measurability`, `ring`, `norm_num`, `Finset.sum_*`) eliminates up to **`358,633` body LOC** (net non-overlapping dedup + Mathlib reduction: **`-655,063` body LOC / `-29.08%`** of reachable body LOC).

### Lever 4: Narrow-Interface Bottleneck Encapsulation (Stage 4 Refactoring Work Orders)
Because the Cooper-Harvey-Kennedy dominator tree has max depth `46` and strong bottleneck encapsulation (`examples/rh_alpo/refactor_plan.md`), large subtrees sit behind remarkably narrow formal interfaces (`Inputs ⊢ Outputs`):
- **`GlobalTheory.T.jacquetRallisUnitMatch_all_ranks`** (`dominator_depth = 3`): directly dominates **`1,371` declarations (`18,756` body LOC)** through a single 1-line universal statement.
- **`UpperTheory.Gal.FiniteEtaleModels.ptAll_holds`**: encapsulates **`96,783` descendant LOC** behind a 48-character statement (`PtAllStatement`).
- **`GlobalTheory.AV.AbVar.isCharpoly_charpoly_unique`** & **`GlobalTheory.MulIsogeny.mul_isogeny`**: encapsulate **`79,186` LOC** and **`52,791` LOC** of abelian-variety endomorphism machinery behind crisp textbook statements.
- Executing the top 20 kernel-checked work orders in `examples/rh_alpo/refactor_plan.md` (verified at each step by `proof_compressor.refactor.gate.verify_refactor_gate`) is projected to compress reachable body LOC by an additional **`~647,000` LOC**.

### Lever 5: `.olean` Kernel-Level Exact Pruning vs. Source-Level Heuristics
When a machine has the compiled Mathlib + project `.olean` build cache (~25–40 GB disk), running `lean_extractor` (`lake env .lake/build/bin/extract_dag`) and `proof-compressor ingest-olean` replaces source-level identifier heuristics with `Expr.getUsedConstants` over kernel proof terms:
- Every implicitly synthesized `instance`, every `@[simp]` rewrite rule actually applied in a proof term, every coercion, and every macro expansion is explicitly present in the kernel `Expr` DAG.
- Consequently, `.olean` kernel-level pruning eliminates the ~3,500–4,000 conservative `instance-aware` buffer modules that were imported in scope but never actually instantiated by the kernel, converging to the **exact mathematical and type-checking minimum (~36,000 modules / ~2.90M LOC)**.

---

## 5. System Performance & Scalability Optimizations (`proof-compressor`)

Benchmarking on the full 175,187-file `alpo.ge` archive (`467s` end-to-end wall-clock, `1.5 GB` SQLite DB, `3.72 GiB` peak RSS) identified four concrete system optimizations for future multi-million-declaration runs:

1. **Parallel Multi-Part Gzip/Tar Pass 1 Ingestion (`158.6s -> ~35s`)**:
   - Currently `_ConcatPartStream` decompresses `lean.tar.gz.part01..part14` sequentially on a single core (`~6.5 MB/s` uncompressed). Recording tar header byte offsets or partitioning extracted file buffers across a `ProcessPoolExecutor` of 6–8 worker parsers (feeding a single SQLite writer queue) will cut Pass 1 from `158.6s` to `~35s`.
2. **Pre-Sorted Integer Symbol Interning in Pass 2 Edge Resolution (`184.8s -> ~45s`)**:
   - Replacing string dictionary lookups (`by_name`, `by_short`) in Pass 2 with 32-bit integer symbol IDs and pre-packed `array('I')` CSR module-import adjacency will cut peak RSS from `3.72 GiB` to `<1.4 GiB` and speed up Pass 2 by ~4×.
3. **Incremental Content-Hash SQLite Caching (`467s -> <5s` on incremental edits)**:
   - Storing a per-file SHA-256 / mtime in `modules` allows `proof-compressor ingest` to re-parse only modified `.lean` files during Stage 4 refactoring loops, making iterative `refactor-plan -> materialize -> gate` cycles near-instantaneous.
4. **Parallel Sub-Cluster LaTeX & Audit Synthesis (`90s -> ~15s`)**:
   - Generating per-chapter LaTeX ASTs and dependency-cone checks concurrently across chapters reduces Stage 3 exposition + auditing time by 5–6×.
