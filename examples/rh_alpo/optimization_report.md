# Quantitative optimization report: `alpo.ge` Riemann Hypothesis Lean 4 corpus

Measured on the full `alpo.ge` corpus (`data/lean.tar.gz.part01..14`): **175,187 modules**, **15,531,759 non-blank LOC**, **1,061,531 declarations**, **9,003,126 dependency edges**, 239.28 MB `.tar.gz` / 1,030.54 MB uncompressed. Every number below comes from `outputs/rh_full.db` and the `materialize --json` reports of this run; nothing is projected unless a row says so.

> **Change from the previous report.** The source parser used to miss many references: identifiers with Greek/letter-like characters (`hσ`, `Gammaℝ`), `_root_.`-qualified names, declarations whose name starts with a Greek letter (recorded as unresolvable `anon_*` rows), `alias` declarations, field notation on locals (`D.clsHom_surjective`) and types named only in `variable` commands. It also turned proof-local names (`obtain ⟨B, hB⟩`, `intro hτ`, `fun τ =>`) into false edges. With those fixed, the declaration-reachable cone from `Main` is 145,276 modules and 799,064 declarations; the previous report said 35,669 and 183,501. Scored against kernel-level dependencies of 5,071 compiled declarations, 97.6% of the tool's edges are real and it finds 81.4% of the real ones. The pruned archives changed little in size, because instance-aware materialization was already keeping those modules through its closure passes. The old figures for the `decl-exact` core and the projected stages 7-8 are withdrawn.

## 1. Measured compression waterfall

```bash
uv run proof-compressor materialize outputs/rh_full.db --source data/lean.tar.gz.part01 \
  --output-archive outputs/rh_merged.tar.gz --mode instance-aware \
  --collapse-barrels --consolidate-duplicates --strip-comments \
  --external-names mathlib_names.txt \
  --merge-modules --target-module-loc 5500
```

| Stage | Modules | Module reduction | Non-blank LOC | Uncompressed | `.tar.gz` |
| :--- | ---: | ---: | ---: | ---: | ---: |
| Raw archive | 175,187 | 0.00% | 15,531,759 | 1,030.54 MB | 239.28 MB |
| `import` closure of `Main` | 175,184 | -0.00% | 15,531,434 | — | — |
| Declaration-reachable cone (analysis) | 145,276 | -17.07% | 13,427,197 (10,432,497 decl-body LOC) | — | — |
| `instance-aware` + barrel collapse + strip + dedup + comments (`rh_compressed.tar.gz`) | 149,208 | -14.83% | 13,128,024 (-15.48%) | 868.41 MB | 202.29 MB (-15.46%) |
| `--merge-modules` + Phase-B consolidation (`rh_merged.tar.gz`) | **4,685** | **-97.33%** (37.4×) | **12,812,699** (-17.51%) | 815.09 MB | **184.92 MB** (-22.72%) |

Pass details (`rh_merged.tar.gz` run):
- Kept modules: 145,276 declaration-reachable + 887 instance/class support + 24 syntax/tactic support modules, plus modules restored by the definition/`_root_.`/dot-projection closure passes, minus 150 pure forwarding barrels collapsed (751 LOC). Result: 149,208 modules (13,790,616 raw LOC).
- Intra-module stripping: 57,079 unreferenced theorems/lemmas removed (-719,449 LOC), plus top-level `example` blocks.
- Import rewriting: 14,867 dead imports dropped, 68,264 rewritten through collapsed barrels/dropped modules. `open` tokens whose namespace no longer exists are removed, and tokens that a project namespace could shadow are pinned to `_root_.<ns>` (Lean 4 opens only the innermost match).
- Exact-duplicate consolidation: 1,461 pre-merge delegations (-11,133 LOC) + 8,502 Phase-B delegations (-68,517 LOC) = **9,963** (-79,650 LOC). Hoistable potential not applied: 9,674 groups / 13,574 decls / 103,967 LOC.
- Comment/blank stripping: -57,990 lines.
- Module merging: 149,208 → 4,685 modules, -587,150 import lines, -315,325 net LOC; 0 import cycles, 0 dangling imports.
- Merge guards: 53 modules that import only part of Mathlib stay apart from full-Mathlib bundles, and a declaration is kept out of any file where it would capture another module's reference. Across bundle imports, 8,995 references are written out as `_root_.<original name>`, 17 declarations are marked `protected` (with 741 references to them qualified), and 197 sites are left unrepaired. `--external-names` takes the list of every constant of the imported libraries (493,504 for this Mathlib), dumped from Lean with a ten-line script.

## 2. `import` closure vs. declaration reachability

- `Main`'s transitive `import` closure covers **175,184 of 175,187 modules** (15,531,434 LOC). The umbrella barrels `Supplements.Kernels.MainTheoremsAll` / `MainTheoremsCritical` import four `SmallClassNumbers.*` modules that no reachable declaration references.
- Declaration-level reachability from the five `Main` roots: **145,276 modules** (82.93% of modules, 86.45% of LOC), **799,064 declarations** (75.27%), 10,432,497 declaration-body LOC, 6,094,393 edges among them.
- Imported but never referenced: **29,911 modules** (2,104,562 LOC):

| Category | Modules | LOC | Handling |
| :--- | ---: | ---: | :--- |
| Theorem/lemma-only modules | 18,066 | 881,752 | dropped |
| `def`/`structure`/`inductive` modules | 7,023 | 798,442 | dropped unless a kept declaration needs them |
| Bookkeeping helper-lemma modules | 4,130 | 340,350 | dropped |
| `instance`/`class` modules | 518 | 83,025 | kept in `instance-aware` mode (typeclass synthesis has no identifier edge) |
| Zero-declaration barrel/tactic modules | 174 | 993 | pure barrels collapsed; syntax/tactic modules kept |
| **Total** | **29,911** | **2,104,562** | |

Top 10 packages by dead-imported modules:

| Package | Dead-imported modules | Dead-imported LOC | Reachable modules | Reachable body LOC |
| :--- | ---: | ---: | ---: | ---: |
| `Development.AbelianVarietyTheory` | 19,530 | 1,187,738 | 79,657 | 4,620,502 |
| `GroundTheory.HeightsAndTheta` | 2,494 | 196,513 | 3,916 | 252,201 |
| `Development.AutomorphicArithmetic` | 1,774 | 156,277 | 16,657 | 1,262,457 |
| `Development.AutomorphicSpectrum` | 1,515 | 119,233 | 13,632 | 775,251 |
| `Formalism.PeriodIntegrals` | 990 | 71,466 | 3,360 | 272,263 |
| `Formalism.LocalToGlobal` | 677 | 62,226 | 4,824 | 560,221 |
| `Formalism.SharpRestriction` | 368 | 42,401 | 2,725 | 427,095 |
| `ReciprocityTheory.ReductiveGroups` | 355 | 34,265 | 2,444 | 272,374 |
| `GroundTheory.PAdicHodge` | 113 | 27,567 | 113 | 17,020 |
| `Development.WeilBound` | 334 | 22,710 | 6,717 | 612,548 |

## 3. Materialization modes side by side

| Metric | `import-closure` | `decl-exact` | `instance-aware` (`rh_compressed`) | `instance-aware --merge-modules` (`rh_merged`) |
| :--- | ---: | ---: | ---: | ---: |
| Kept modules | 175,187 | 145,276 | 149,208 | 4,685 |
| Dropped modules | 0 | 29,911 | 25,979 | 170,502 |
| Stripped intra-module decls | 171,204 | 76,646 | 57,079 | 57,079 |
| Stripped LOC | 2,302,162 | 828,947 | 719,449 | 719,449 |
| Consolidated duplicates | — | — | 1,461 | 9,963 |
| Final non-blank LOC | 13,229,597 (-14.82%) | 12,598,250 (-18.89%) | 13,128,024 (-15.48%) | 12,812,699 (-17.51%) |
| `.tar.gz` size | — | — | 202.29 MB | 184.92 MB |

`import-closure` and `decl-exact` are dry runs (`--dry-run`). `decl-exact` keeps only declaration-reachable modules and does not compile: it drops instance modules that typeclass synthesis needs implicitly.

## 4. Lean v4.33.1 + Mathlib compile check

**The merged archive has not been compiled in full.** `Main` has not been built from it, so there is no `#print axioms riemannHypothesis` result for this archive yet. What was run against Lean `v4.33.1` + Mathlib `0df444a360ea`:

| Check | Scope | Result |
| :--- | :--- | :--- |
| Targeted `lake build` of this archive | 21 bundles holding the declarations that failed in earlier archives, plus their import closure: 76 of 4,685 modules | 76 built, 0 errors, `lake` exit 0 |
| Standalone compile of pruned modules (earlier iteration of the pruned archive) | 48 random modules that import only Mathlib, each compiled in its original and its pruned form | 48/48 original, 48/48 pruned |
| Kernel axiom audit (earlier iteration of the merged archive) | all 9,216 constants in 26 compiled bundles | only `propext`, `Classical.choice`, `Quot.sound` |
| Source scan of the raw corpus | 175,187 files | no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, `extern`; 124 `decide +kernel` (kernel-checked) |

The targeted set is biased toward bundles that used to fail, so it says the known failure classes are fixed, not that the remaining 4,609 modules build. Earlier iterations of the archive failed on 22, then 16, 12 and 9 of those bundles. The causes, all in this tool and all fixed with regression tests:

- declarations with Greek-initial names recorded as anonymous, and `alias` not parsed as a declaration;
- references through field notation (`D.clsHom_surjective`), `@[reassoc]`/`@[simps]` generated lemmas and `variable` binder types not counted as dependencies;
- `example` blocks kept after the lemmas they cite were stripped;
- `open X` lines left pointing at pruned namespaces, or hijacked by a project namespace of the same name once merging made it visible;
- modules that import part of Mathlib merged into bundles that import all of it (extra instances change elaboration);
- name capture: inside `namespace P`, a bare `r` resolves to `P.r` before Mathlib's `r`, and merging makes more `P.r` visible.

Known residual risk in this archive: 197 capture sites were not rewritten (the name is also bound locally in the same declaration, or was not found as a whole identifier), and at 123 sites an overloaded name has one candidate that is now `protected`, where the source alone does not show which candidate Lean chose. On a 5,071-declaration sample scored against kernel dependencies, the dependency graph has 97.6% precision and 81.4% recall; the materializer's closure passes recover most of the missed edges, but a missed edge to a stripped lemma is the most likely kind of error in a full build.

Build size, measured on compiled bundles: `.lake/build` is about 169x the source size uncompressed (roughly 137 GB for this archive). APFS compression with `afsctool -c -T LZFSE` reduces it 4.7x, and Lean and lake accept the compressed files.

## 5. Remaining reduction levers

- **Exact duplicates** (same canonical type hash, theorems only): 60,392 groups, 76,303 redundant declarations, 907,765 reducible body LOC.
- **Near duplicates** (signature similarity ≥ 0.85): 37,442 groups, 48,947 declarations, 603,937 LOC.
- **Mathlib absorption candidates** (project theorems over standard Mathlib types): 221,024 declarations, 1,932,003 LOC. This is a heuristic upper bound; each candidate still needs a matching Mathlib lemma.
- Combined estimate: 306,103 declarations / 3,129,698 LOC reducible, 10,432,497 → 7,302,799 declaration-body LOC (-30.0%).

Per-package duplication and bookkeeping (reachable declarations):

| Package | Reachable decls | Body LOC | Exact-dup redundant decls | Exact-dup reducible LOC | Bookkeeping decls | Bookkeeping LOC |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Development.AbelianVarietyTheory` | 337,791 | 4,620,502 | 42,210 | 378,511 | 45,245 | 341,112 |
| `Development.AutomorphicArithmetic` | 78,518 | 1,262,457 | 6,676 | 82,054 | 6,977 | 77,287 |
| `Development.AutomorphicSpectrum` | 57,399 | 775,251 | 7,673 | 147,308 | 7,468 | 59,023 |
| `Development.WeilBound` | 50,329 | 612,548 | 4,387 | 56,481 | 4,019 | 23,115 |
| `Formalism.LocalToGlobal` | 53,640 | 560,221 | 2,906 | 24,999 | 5,591 | 31,332 |
| `Formalism.SharpRestriction` | 36,897 | 427,095 | 1,576 | 12,959 | 3,104 | 17,943 |
| `Formalism.HermitianCurvature` | 29,020 | 310,170 | 1,809 | 13,898 | 2,293 | 12,367 |
| `ReciprocityTheory.ReductiveGroups` | 21,610 | 272,374 | 1,938 | 20,588 | 2,597 | 17,938 |
| `Formalism.PeriodIntegrals` | 24,424 | 272,263 | 2,026 | 20,404 | 2,644 | 14,980 |
| `GroundTheory.HeightsAndTheta` | 18,280 | 252,201 | 896 | 10,945 | 1,557 | 11,288 |
| `Development.ResolutionOfSingularities` | 7,590 | 116,064 | 174 | 1,619 | 830 | 7,162 |
| `GroundTheory.AutomorphicForms` | 7,970 | 91,329 | 39 | 330 | 1,102 | 5,914 |
| `CompanionTheory.SpectralGeometry` | 5,721 | 82,589 | 681 | 15,341 | 828 | 6,297 |
| `Development.EtaleCohomology` | 9,127 | 73,462 | 972 | 5,977 | 682 | 3,466 |
| `GroundTheory.ProfiniteCohomology` | 5,153 | 53,363 | 40 | 423 | 662 | 5,123 |

`Development.AbelianVarietyTheory` holds 42.3% of reachable declarations, 44.3% of reachable body LOC and 46.2% of exact-duplicate reducible LOC, which makes it the largest single refactoring target.

Stage 4 work orders (`refactor_plan.md`): 20 targets with a combined planner estimate of 2,376,156 LOC. The estimate is the planner's heuristic, not a measured result. Dominator tree depth is 48; 262 non-trivial SCCs (largest 38). Top work orders:

| Order | Scope | Internal LOC | Declarations | Interface width | Est. savings |
| :--- | :--- | ---: | ---: | ---: | ---: |
| `cluster-34` | Development / Abelian Variety Theory: se Good | 4,621,552 | 337,931 | 500 | 1,461,267 |
| `cluster-52` | Development / Automorphic Arithmetic: zel | 1,262,695 | 78,545 | 500 | 189,404 |
| `cluster-33` | Development / Automorphic Spectrum: whit Heredity | 775,345 | 57,403 | 500 | 210,751 |
| `cluster-32` | Development / Weil Bound: segment Representation | 612,767 | 50,371 | 500 | 91,915 |
| `cluster-105` | Formalism: gluing mass holds | 564,142 | 53,880 | 500 | 84,621 |
| `cluster-103` | Formalism: inert conditions hold | 428,351 | 36,930 | 500 | 64,252 |
| `cluster-102` | Formalism: lattice average induction | 310,929 | 29,081 | 500 | 46,639 |
| `cluster-104` | Formalism / Period Integrals: row lattice mass | 273,269 | 24,468 | 500 | 42,802 |

## 6. Run timings

- Ingest: 416s (pass 1 parse 257s, pass 2 resolution 158s); analysis 99s; exposition 124s.
- `rh_compressed.tar.gz`: 396s. `rh_merged.tar.gz`: 1218s. Both stream straight from the multi-part archive with no extraction to disk.
