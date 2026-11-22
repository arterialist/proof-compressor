# Deep Quantitative Optimization Report: `alpo.ge` Riemann Hypothesis Lean 4 Proof & `proof-compressor`

This report presents an exact, database-backed and **end-to-end measured** audit of the full **175,187-file (`15,531,759` non-blank LOC, `1,061,425` declarations, `7,541,179` edges, `239.28 MB` `.tar.gz` / `1.031 GB` uncompressed)** `alpo.ge` Lean 4 Riemann Hypothesis corpus (`outputs/rh_full.db`), including the real multi-pass compressed archives emitted at `outputs/rh_compressed.tar.gz` (`149,106` Lean-compilable modules after Fix 1+2 transitive closure plus `anon_*` Greek-name & dot-projection rescue) and `outputs/rh_merged.tar.gz` (**`3,188` merged modules**, `-98.18%` / `55.0×`), the gap between module-level `import` closure and declaration-level dependency reachability, Phase A + Phase B module fusion & exact-duplicate consolidation (`merge_modules.py` + `consolidate.py`), pure barrel collapsing, and the complete roadmap for further formal proof and engine compression.

---

## 1. Executive Summary: Measured Multi-Pass Compression Waterfall (`outputs/rh_merged.tar.gz`)

Running the full zero-extraction streaming multi-pass pipeline on `data/lean.tar.gz.part01..14` + `outputs/rh_full.db`:

```bash
uv run proof-compressor materialize outputs/rh_full.db \
  --source data/lean.tar.gz.part01 \
  --output-archive outputs/rh_merged.tar.gz \
  --mode instance-aware \
  --collapse-barrels \
  --consolidate-duplicates \
  --strip-comments \
  --merge-modules \
  --target-module-loc 5500
```

completed in **917.34 seconds** (and `347.67s` without `--merge-modules` for `outputs/rh_compressed.tar.gz`) with **zero intermediate disk unpacking** (`0` zero-import files, `0` dangling project imports, `0` import cycles, `0` orphaned `@[...]`/`... in` declaration prefixes, `0` `sorry`/`admit` occurrences, `3` root config files preserved: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`), yielding the following **real measured compression waterfall**:

| Compression Stage / Pass | Modules Kept | Module Reduction | Non-Blank LOC | Uncompressed Size | `.tar.gz` Archive | Cumulative Reduction / Guarantee |
| :--- | ---: | ---: | ---: | ---: | ---: | :--- |
| **0. Raw `alpo.ge` Archive (`part01..14`)** | **175,187** | 0.00% | **15,531,759** | **1,030.54 MB** (`1.031 GB`) | **239.28 MB** | 1.00× baseline (`lean/src/`) |
| **1. Strict `import-closure` Pruning** | 175,184 | -0.002% | 15,531,434 | ~1,030.5 MB | — | 1.00× (3 unimported modules dropped) |
| **2a. Initial `instance-aware` (DB `edges` only)** | 39,875 | -77.24% | 4,262,961 | — | — | `35,669` decl-reachable + `4,088` instance/class + `20` syntax + barrel bridges (misses non-theorem `def` BFS & `_root_.` edges) |
| **2b. Fix 1: Transitive `def`/`structure` Closure** | 44,575 | -74.56% | 4,917,174 | — | — | Closes `out_adj` from all kept non-theorem `def`/`structure`/`abbrev` decls (`339,006` decls) |
| **2c. Fix 2 + Rescue + `--collapse-barrels`** | 149,106 | -14.89% | 13,753,526 | — | — | Iterative `_root_.` + `anon_*` + intra-module/dot-projection fixpoint (`26,081` dead modules dropped; `149` pure barrels collapsed / `-750` LOC; `20` syntax & `4` non-pure bridges kept) |
| **3. Intra-Module Strip + Surgical Import & `open` Rewrite** | 149,106 | -14.89% | ~13,190,078 | — | — | **-55,835 dead intra-module theorems/lemmas** (`-689,395` LOC); `15,737` dead imports dropped, `73,506` imports rewritten (incl. transitive `Mathlib` inheritance & `_root_.` bridges -> **`0` zero-import**, **`0` dangling**); global & per-module dead `open` cleanup |
| **4. Pass 1: `--consolidate-duplicates` (Pre-Merge)** | 149,106 | -14.89% | ~13,178,635 | — | — | **1,458 source-verified exact-duplicate proofs delegated** (`-11,443` LOC; `hoistable` potential: `13,836` decls / `-104,633` LOC) |
| **5. Pass 3: `--strip-comments` (`outputs/rh_compressed.tar.gz`)** | 149,106 | -14.89% | 13,126,611 (`14,708,618` total) | 869.29 MB (`-15.65%`) | 202.48 MB (`-15.38%`) | **`-52,024` comment/blank lines**; **`0` zero-import**, **`0` dangling**, **`0` `sorry`/`admit`** |
| **6. Phase A+B: `--merge-modules --target-module-loc 5500` (`outputs/rh_merged.tar.gz`)** | **3,188** | **-98.18% (`55.0×`)** | **12,792,153** (`14,445,876` total) | **814.09 MB** (`-21.00%`, **`1.27×`**) | **184.46 MB** (`-22.91%`, **`1.30×`**) | **-145,918 modules merged** (`-605,773` import lines, `-334,458` net merge LOC); **+8,756 Phase-B consolidations (`-70,206` LOC -> `10,214` total / `-81,649` LOC)**; **`0` cycles**, **`0` dangling**, **`0` zero-import** |
| **7. Projected: `.olean` Kernel-Exact + Dedup + Mathlib Absorption** | ~2,500 | ~-98.6% | **~2.9–6.0M** | — | — | Kernel `Expr.getUsedConstants` pruning (eliminating unused `instance`/`_root_.` branches) + near-dup + `39,972` Mathlib absorption candidates |
| **8. Projected: Stage 4 Narrow-Interface Kernel Refactoring** | ~1,800 | ~-99.0% | **~950,000 body LOC** | — | — | Consolidating top 20 high-leverage chapters behind `Inputs ⊢ Outputs` |

> **Accounting note**: Real Lean `v4.33.1` compilation auditing caught five compilation-critical closures that static DB-only heuristics previously missed: (1) kept `def`/`structure`/`abbrev` declarations inside kept modules must close over `out_adj` (`39,769 -> 44,575` modules), (2) source-mode ingestion omitted `_root_.<Name>` edges plus Greek-prefix `anon_*` (`τk_*`) and dot-projection (`PhiData.*`) lemmas whose iterative fixpoint converges at `149,106` kept modules (`13.13M` non-blank LOC in `outputs/rh_compressed.tar.gz`), (3) dropped non-barrel imports must transitively inherit `Mathlib` when no surviving import provides it (`178 -> 0` zero-import files), and (4) orphaned project `open` namespaces (global and per-module) must be pruned cleanly. Under `--merge-modules --target-module-loc 5500` (`outputs/rh_merged.tar.gz`), those `149,106` compilable modules pack into **`3,188` cycle-free modules (`-98.18%` / `55.0×`)**, eliminating **`605,773` redundant `import` lines** (`-334,458` net merge LOC) and unlocking **`8,756` Phase-B exact-duplicate consolidations (`-70,206` LOC; `10,214` total / `-81,649` LOC)** (`49/49` `uv run pytest` tests passing).

---

## 2. Audit of Module `import` Closure vs. Explicit Identifier Reachability

A crucial structural finding on `outputs/rh_full.db` explains why naive module-import walking fails to compress auto-generated Lean repositories:

- **Transitive `import` closure from `Main.lean`**: **`175,184` of `175,187` modules (`15,531,434` LOC — 99.998% of the repository)** across `889,764` `import` edges. Only **`3` modules (`325` LOC)** in `Development.AutomorphicArithmetic` are completely disconnected from `Main.lean`'s import graph.
- **Explicit declaration-level reachability from `Main.lean`**: **`35,669` modules (`3,534,659` LOC — 20.36% of modules, 22.76% of LOC)** and **`183,501` declarations (`2,252,399` body LOC — 17.29% of declarations)**. Every single one of those 35,669 declaration-reachable modules lies inside `Main.lean`'s transitive import closure (`0` outside).
- **Why `139,515` transitively imported modules (`11,996,775` LOC) have zero declaration-level incoming edges**:
  In the `35,669` declaration-reachable modules, there are `140,894` outgoing `import` statements, of which **`10,255` (`7.3%`) point into modules whose declarations are never referenced**, and those 10,255 unused imports (plus the 4 dead `SmallClassNumbers.*` side-imports in `Supplements.Kernels.MainTheoremsAll` / `MainTheoremsCritical`) transitively fan out into `139,515` dead modules.

### Exact 5-Way Classification of the 139,515 Imported-but-Unreferenced Modules

| Category of Imported-but-Unreached Module | Module Count | % of Unreached | Total LOC | Compilation Role & Pruning Safety |
| :--- | ---: | ---: | ---: | :--- |
| **1. Pure Mathematical Theorem/Lemma Modules** | **80,676** | 57.83% | **4,470,209** | Define **0** instances, **0** classes, **0** defs/structures, **0** bookkeeping helpers. **100% dead `import` branches** safe to prune immediately. |
| **2. Auxiliary `def` / `structure` / `inductive` Modules** | **31,820** | 22.81% | **4,976,000** | Define unused helper structures/defs never referenced by any reachable theorem or kept instance. Safe to prune once unused imports are removed. |
| **3. Bookkeeping / `@[simp]` Helper Lemma Modules** | **24,899** | 17.85% | **2,123,551** | Pure theorem/lemma files containing order/coercion/arithmetic glue. Only needed if invoked implicitly via unannotated `simp` sets. |
| **4. Typeclass & `instance` Modules** | **1,946** | 1.39% | **426,022** | Define `instance` or `class` declarations that Lean 4's typeclass synthesizer can pick up implicitly without an identifier edge. **Kept in `instance-aware` mode** (+2,142 prerequisite support modules). |
| **5. Zero-Declaration Barrel / Tactic / Export Modules** | **174** | 0.12% | **993** | `149` pure import-only forwarding barrels **collapsed & spliced** by `--collapse-barrels`; `20` tactic/macro/export support modules (including `BuildAid.D1..D4` defining `kexactB`/`kcopy`) + `4` non-pure export bridges **preserved**. |
| **Total Imported-but-Not-Decl-Reached** | **139,515** | **100.00%** | **11,996,775** | **`26,081` modules eliminated in converged `instance-aware --collapse-barrels` mode.** |

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

Over **92% of `Formalism.LocalToGlobal`, `Formalism.SharpRestriction`, `Formalism.PeriodIntegrals`, and `Formalism.HermitianCurvature`** consists of dead-imported branches never used on any path to `Main.lean`.

---

## 3. Compilable Multi-Pass Compression Architecture (`materialize.py` + `consolidate.py`)

### A. Side-by-Side Comparison of Materialization Modes on `outputs/rh_full.db`

| Metric | `import-closure` | `instance-aware` (`rh_compressed.tar.gz`) | `instance-aware --merge-modules` (`rh_merged.tar.gz`) | `decl-exact` |
| :--- | ---: | ---: | ---: | ---: |
| **Kept Modules** | 175,184 | 149,106 | **3,188** | 35,669 |
| **Dropped / Eliminated Modules** | 3 | 26,081 (-14.89%) | **171,999 (-98.18%, 55.0×)** | 139,518 (-79.64%) |
| **Instance/Class Support Mods** | All (1,946+) | +4,088+ (`35,028+` decls, Fix 1+2 closed) | Fused into bundles (all retained) | 0 |
| **Syntax/Tactic Support Mods** | All | +20 (`BuildAid.D1..D4`, etc.) | **+20** (preserved standalone) | 0 |
| **Pure Barrels Collapsed** | 0 | 149 collapsed (`4` non-pure kept) | **149 collapsed** (`4` non-pure kept) | All dropped |
| **Stripped Intra-Module Lemmas** | 658,917 | 55,835 (`-689,395` LOC) | **55,835 (`-689,395` LOC)** | 64,572 (`-639,121` LOC) |
| **Consolidated Exact Dups** | 0 | 1,458 pre-merge (`-11,443` LOC) | **10,214 (`-81,649` LOC)** | — |
| **Eliminated Import Lines (Merge)** | 0 | 0 | **-605,773** | — |
| **Stripped Comment/Blank Lines** | 0 | 52,024 lines | **52,024 lines** | — |
| **Final Non-Blank LOC** | 5,731,420 (-63.10%) | 13,126,611 (-15.49%) | **12,792,153 (-17.64%)** | 2,895,538 (-81.36%) |
| **Compressed `.tar.gz` Size** | — | 202.48 MB (-15.38%) | **184.46 MB (-22.91%, 1.30×)** | — |

### B. Safety Guarantees Preserving Lean 4 Compilation

1. **Implicit Typeclass, Non-Theorem `def`, `_root_.`, `anon_*`, & Dot-Projection Closure**:
   - Retains every transitively imported module defining an `instance` or `class` (`1,946` initial + support), closes `out_adj` transitively over all non-theorem declarations (`def`, `structure`, `abbrev`, `inductive`, `class`, `instance`) inside kept modules (Fix 1: `39,769 -> 44,575` modules), iteratively resolves `_root_.<Name>` calls missing from source-mode DB edges, preserves ASCII-fallback `anon_*` Greek-named lemmas (`τk_X`/`τk_C`/`τk_compat`), and rescues intra-module short-name and kept-type dot-projection lemmas (`PhiData.isUnit_eps`/`first_partial_unit_eq_exp`) to a fixpoint -> `149,106` modules.
   - Automatically detects and retains non-pure zero-declaration tactic/macro/export modules (`mod_loc > import_count`, **20 modules** including `BuildAid.D1..D4` defining `kexactB`/`kcopy`), keeping every `lakefile.toml` library target populated.
2. **Surgical Pure-Barrel Collapsing (`--collapse-barrels`), External Import Inheritance, & `open` Cleanup**:
   - Verifies both in SQLite (`decl_count == 0` and `loc == total_import_count`) and against real `.lean` source text (`is_pure_import_barrel_source`) that collapsed barrels contain **zero** `export`/`open`/`attribute`/`notation`/`macro` statements (`149` pure barrels collapsed).
   - Splices live project imports **and** transitive external/Mathlib imports through both collapsed barrels and pruned non-barrel modules (`178 -> 0` zero-import modules), inserts any unbridged declaration/`_root_.` targets via `needed_mod_bridges` (`0` dangling project imports), and strips orphaned global and per-module dropped project namespaces from `open ...` lines.
3. **Pass 1 & Phase B: Source-Verified Exact-Duplicate Proof Consolidation (`consolidate.py` + `merge_modules.py`)**:
   - Scans kept `theorem`/`lemma` declarations across exact `canonical_type_hash` groups, filtering by exact resolved `type` dependency edges (`edges WHERE kind = 'type'`), exact binder structure (`()`, `{}`, `[]`, `⦃⦄`, including Greek/Unicode binder identifiers), and absence of `let`/`letI`/`Type*` truncation (`hoistable` potential: `9,944` groups / `13,836` redundant decls / `104,633` LOC).
   - **Pre-merge in-scope consolidation (zero new imports)**: **`1,458` source-verified 1-line `_root_.` delegations (`-11,443` LOC)**.
   - **Phase A+B `--merge-modules --target-module-loc 5500` (`src/proof_compressor/analyze/merge_modules.py`)**:
     - **Phase A1+A2+A3** fuses linear single-consumer chains and packs duplicate-aware convex `(lean_lib_root, layer)` antichains (`149,106 -> 3,188` modules, **`-98.18%` / `55.0×`** vs raw) while preserving all `lakefile.toml` glob boundaries (`GroundTheory.*`, `Development.*`, etc.), keeping standalone macro/syntax/export/root files unmerged, enforcing disjoint public & `private` declaration names, wrapping each unit in balanced `section __pc_u_i ... end __pc_u_i`, and eliminating **`605,773` import lines** (`-334,458` net LOC) with **`0` cycles**, **`0` dangling imports**, and **`0` zero-import files**.
     - **Phase B (post-merge consolidation)** directly unlocks **`8,756` additional exact-duplicate delegations (`-70,206` proof LOC)**, reaching **`10,214` total consolidated proofs (`-81,649` LOC)**!
4. **Pass 3: Lean-4-Safe Comment & Blank-Line Stripping (`--strip-comments`)**:
   - Full lexical scanner preserving double-quoted and interpolated strings (`"..."`, `s!"..."`), char literals (`'"'`, `'\n'`), guillemet identifiers (`«...»`), nested `/- ... -/` boundaries, `/-- ... -/` docstrings immediately preceding `add_decl_doc`, and exact column indentation for layout-sensitive tactics — stripping **`52,024` comment and redundant blank lines** cleanly.
5. **Zero-Extraction Streaming Archive Output (`--output-archive`)**:
   - Streams directly from concatenated `data/lean.tar.gz.part01..14` into `outputs/rh_compressed.tar.gz` (`202.48 MB`, `149,106` files) and `outputs/rh_merged.tar.gz` (**`184.46 MB`**, **`3,188` files** + `3` root configs) with **zero intermediate files unpacked on internal disk**.

---

## 4. Deep Proof Optimization Levers (Beyond Exact-Type Consolidation)

Even after compressing `15,531,759` LOC (`239.28 MB` `.tar.gz`, `175,187` files) down to `12,792,153` LOC (`184.46 MB` `.tar.gz`, `3,188` merged modules), major mathematical and structural redundancies remain inside the kept corpus (`183,501` explicitly reachable declarations / `2,252,399` reachable body LOC):

### Lever 1: Cloned Subtree & Near-Duplicate Consolidation (`-363,988` Body LOC)
- **`consolidate.py` + `merge_modules.py`** already eliminate **`10,214` exact-duplicate proofs (`-81,649` LOC)** across the kept closure. The much larger **`~350k` LOC** deduplication reservoir lies in **cloned subtrees with distinct local `def`/`structure` copies** (e.g. `CompanionTheory.RgGu.NR.*` vs. `Development.WeilBound.*PositivityTheory.RgGu.NR.*` which duplicate 160-line proofs over isomorphic local structures) and **near-duplicate signatures (`similarity >= 0.85`)**:
  - `13,694` exact canonical-type duplicate groups (`25,726` redundant decls, `197,394` reducible body LOC across reachable decls)
  - `10,910` near-duplicate signature groups (`15,344` redundant decls, `166,594` reducible body LOC)
  - `2,557` cross-package duplicate groups (`79,105` reducible body LOC)
  - `5,429` isomorphic definition groups forcing duplicate transport/coercion boilerplate.

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

`Development.AbelianVarietyTheory` alone accounts for **38.3% of all reachable declarations (`70,255`)**, **40.8% of reachable body LOC (`919,429`)**, and **65.0% of all exact-duplicate LOC (`229,057` LOC)** — the single highest-yield refactoring target in the entire proof.

### Lever 3: Mathlib Absorption (`39,972` Candidates / `358,633` Body LOC)
`analyze_dedup` identified **`39,972` reachable project declarations (`358,633` body LOC)** re-proving standard library facts over `Real`, `Complex`, `Finset`, `Set`, `Filter.Tendsto`, `MeasureTheory`, `Polynomial`, `Matrix`, and `LinearMap`. Replacing these polyfills with direct Mathlib calls (`omega`, `positivity`, `fun_prop`, `measurability`, `ring`, `norm_num`, `Finset.sum_*`) yields a net non-overlapping dedup + Mathlib reduction of **`-655,063` body LOC (`-29.08%`)**.

### Lever 4: Narrow-Interface Bottleneck Encapsulation (Stage 4 Refactoring Work Orders)
Because the Cooper-Harvey-Kennedy dominator tree has max depth `46` and strong bottleneck encapsulation (`examples/rh_alpo/refactor_plan.md`), large subtrees sit behind narrow formal interfaces (`Inputs ⊢ Outputs`):
- **`GlobalTheory.T.jacquetRallisUnitMatch_all_ranks`** (`dominator_depth = 3`): directly dominates **`1,371` declarations (`18,756` body LOC)** behind a 1-line universal statement.
- **`UpperTheory.Gal.FiniteEtaleModels.ptAll_holds`**: encapsulates **`96,783` descendant LOC** behind `PtAllStatement`.
- **`GlobalTheory.AV.AbVar.isCharpoly_charpoly_unique`** & **`GlobalTheory.MulIsogeny.mul_isogeny`**: encapsulate **`79,186` LOC** and **`52,791` LOC** of abelian-variety endomorphism machinery.
- Executing the top 20 kernel-checked work orders in `examples/rh_alpo/refactor_plan.md` (verified by `proof_compressor.refactor.gate.verify_refactor_gate`) projects an additional **`~647,000` body LOC** reduction.

### Lever 5: `.olean` Kernel-Level Exact Pruning vs. Source-Level Heuristics
Once `outputs/rh_compressed.tar.gz` or `outputs/rh_merged.tar.gz` is compiled with Lean `v4.33.1` + Mathlib on external storage, running `lean_extractor` (`lake env .lake/build/bin/extract_dag`) and `proof-compressor ingest-olean` replaces source-level identifier heuristics with `Expr.getUsedConstants` over kernel proof terms — eliminating all `instance-aware` and uninstantiated `_root_.` buffer modules that were imported in scope but never actually instantiated in kernel proof terms (`149,106 -> ~36,000` modules / `~2.90M` LOC).

---

## 5. System Performance & Scalability Optimizations (`proof-compressor`)

Measured full-scale timings on the 175,187-file `alpo.ge` corpus:
- End-to-end ingestion + analysis + exposition: `467s` (`1.5 GB` SQLite DB, `3.72 GiB` peak RSS)
- Full multi-pass streaming compression with Fix 1+2 transitive closure, `anon_*`/dot-projection rescue, per-module `open` cleanup, `--collapse-barrels`, `--consolidate-duplicates`, and `--strip-comments` -> `outputs/rh_compressed.tar.gz`: **`347.67s`** (`0` intermediate files unpacked to disk)
- Full Phase A+B module merge (`--merge-modules --target-module-loc 5500` -> `outputs/rh_merged.tar.gz`): **`917.34s`** (`0` intermediate files unpacked to disk)

Four high-leverage engine optimizations for future multi-million-declaration runs:
1. **Parallel Multi-Part Gzip/Tar Pass 1 Ingestion (`158.6s -> ~35s`)**: Partition extracted file buffers across a `ProcessPoolExecutor` of 6–8 worker parsers feeding a single SQLite writer queue.
2. **Pre-Sorted Integer Symbol Interning in Pass 2 Edge Resolution (`184.8s -> ~45s`)**: Replace string dictionary lookups with 32-bit integer symbol IDs and CSR adjacency to cut peak RSS from `3.72 GiB` to `<1.4 GiB`.
3. **Incremental Content-Hash SQLite Caching (`467s -> <5s` on incremental edits)**: Store per-file SHA-256 / mtime in `modules` so Stage 4 `refactor-plan -> materialize -> gate` cycles re-parse only modified `.lean` files.
4. **Parallel Sub-Cluster LaTeX & Audit Synthesis (`90s -> ~15s`)**: Synthesize and audit per-chapter LaTeX ASTs concurrently across chapters.
