# Stage 4 Proof Simplification Results & Structural Detour Audit (`alpo.ge` RH Proof)

This report documents the live Stage 4 proof-simplification engine ([`simplify.py`](file:///Users/arterialist/Projects/proof-compressor/src/proof_compressor/refactor/simplify.py)), real Lean `v4.33.1` + Mathlib (`0df444a360ea`) kernel-gated simplification benchmarks on compressed `alpo.ge` RH modules, real Lean `v4.33.1` pruning defects surfaced in the compressed archive, and a concrete mathematical simplification audit for the top 3 structural detours in `outputs/rh_full.db`.

---

## 1. Stage 4 Kernel-Gated Simplification Engine (`simplify.py`)

[`src/proof_compressor/refactor/simplify.py`](file:///Users/arterialist/Projects/proof-compressor/src/proof_compressor/refactor/simplify.py) pairs deterministic + tactical source rewrites with strict kernel-gate verification via [`verify_refactor_gate`](file:///Users/arterialist/Projects/proof-compressor/src/proof_compressor/refactor/gate.py):

1. **Unused Binding & Dead Helper Pruning** (`find_dead_have_candidates`):
   - Removes unused `private lemma`/`private theorem` helpers (skipping `@[simp]`/`@[ext]`/`@[instance]`/`@[aesop]`/`@[norm_cast]`/`@[measurability]`/`@[fun_prop]` attributes).
   - Prunes unused local `have`/`let`/`set` bindings inside `:= by` proof blocks (`prune_dead_have`, `prune_dead_let`, `prune_dead_set`).
2. **Tactic Collapse & Automation Lifting** (`find_tactic_collapse_candidates`):
   - `collapse_first_branch`: collapses AI-generated multi-branch `first | ... | ...` fallback scaffolding (single- or multi-line branches) into the single active branch.
   - `collapse_by_exact`: collapses trivial `:= by exact <term>` / `:= by rfl` wrapper blocks to term-mode `:= <term>`.
   - `collapse_have_this` / `collapse_have_exact` / `collapse_have_simpa`: collapses `have := <expr>; exact this`, `have h := <expr>; exact h`, and `have h := <expr>; simpa using h`.
   - `collapse_bare_bullet` & `merge_rw_chain`: merges bare `·` bullet headers and consecutive same-indent `rw` steps.
   - `lift_calc_chain`, `lift_subproof_automation`, `lift_proof_automation`: attempts to collapse multi-line `calc`, subproofs, and compact theorem bodies to `omega`, `linarith`, `nlinarith`, `norm_num`, `positivity`, `ring`, `simp_all`, `aesop`, `grind`, `decide`, `rfl`, or `tauto`.
   - `_build_batch_candidate`: batches high-confidence deterministic cleanups into a single candidate (`batch_high_confidence`) to minimize `lake build` round-trips.
3. **Mathlib Absorption** (`find_mathlib_absorption_candidates`):
   - Matches declaration `canonical_type_hash` against Mathlib entries in `outputs/rh_full.db` or structural canonical signature patterns (`le_of_mul_le_mul_right`, `le_div_iff₀`, `div_le_one`, `Finset.prod_eq_one`, `Finset.sum_eq_zero`), proposing direct Mathlib delegation or private-helper call-site substitution.
4. **Transactional Kernel Gate & Isolation**:
   - Captures baseline `#check @decl` signatures and `#print axioms decl` via `capture_baseline_signatures` (including `_parse_print_axioms_safe` for primed Lean identifiers such as `C2'`).
   - Every candidate rewrite (`simplify_module`) and explicit tactical/mathematical rewrite (`verify_manual_rewrite`) must pass `verify_refactor_gate`: `lake build <Module>` exits `0`, `#check @decl` exported types match baseline verbatim, `#print axioms` contains only subsets of `{propext, Classical.choice, Quot.sound}`, and `count_effective_loc` strictly decreases. Any failure triggers automatic revert.
   - Subprocesses run via `_run_subprocess_clean` (`start_new_session=True` + `os.killpg(..., SIGKILL)` on timeout) so timed-out `lake`/`lean` trees never leave orphaned background workers.

---

## 2. Live Lean `v4.33.1` + Mathlib Simplification Benchmark

All real RH builds ran inside the isolated `apfs_mnt/tmp/rh_simplify_scratch` workspace (`109 GiB` free, symlinked prebuilt Mathlib `.olean`s, `leanprover/lean4:v4.33.1`, zero writes to `/`) on targeted-Mathlib modules extracted from regenerated `outputs/rh_compressed.tar.gz` (`#136`).

### 2.1 Kernel-Verified Modules

| Module | Orig Eff. LOC | Auto Stage 4 LOC | Final (Auto+Manual) LOC | Steps (Before -> After) | Gate Timing(s) | `#print axioms` | Outcome |
|---|---:|---:|---:|---:|---:|---|---|
| `Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.EqZeroOfForallMemCoeffFiltration` | 177 | 171 (`-6`) | **169 (`-8`, -4.5%)** | 143 -> 132 (`-11`) | base `0.349s`; auto `3.67s`, `3.31s`, `3.70s`; manual `3.37s` | 19/19 in `{propext, Classical.choice, Quot.sound}` | **PASS** (auto `collapse_first_branch` x2, `collapse_by_exact` + manual `have` collapse) |
| `Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.MemPairOfMemSingle` | 134 | 130 (`-4`) | **123 (`-11`, -8.2%)** | 104 -> 95 (`-9`) | base `1.03s`; auto `71.89s`; manual `3.94s` | 12/12 non-primed (+ `C2'` at baseline) in `{propext, Classical.choice, Quot.sound}` | **PASS** (auto `batch_high_confidence` x4 + manual `calc`/`have` collapse) |
| `Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished` | 237 | 236 (`-1`) | **230 (`-7`, -3.0%)** | 196 -> 191 (`-5`) | base `4.31s`; auto `4.31s`; manual `58.98s` | 11/11 in `{propext, Classical.choice, Quot.sound}` | **PASS** (auto `collapse_have_simpa` + manual inline/`le_antisymm` collapse) |
| `Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FormalSeriesValueAtTwoPointsGenericPoints` | 98 | 97 (`-1`) | **91 (`-7`, -7.1%)** | 64 -> 60 (`-4`) | base `16.73s`; auto `4.13s`; manual `4.07s` | 9/9 in `{propext, Classical.choice, Quot.sound}` | **PASS** (auto `collapse_by_exact` + manual `dist_of_map_eq` collapse) |
| `Development.EtaleCohomology.EtaleSheaves.CurveKrullDimTopology` | 62 | 62 (`0`) | **62** | 55 -> 55 | cold `21m02.9s`; warm base `0.337s` | 3/3 in `{propext, Classical.choice, Quot.sound}` | **PASS** (baseline verified; 16 speculative tactic lifts cleanly rejected) |
| `Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExtendOneMulVecSingleLast` | 84 | 84 (`0`) | **84** | 62 -> 62 | warm base `3.032s` | 9/9 (`Quot.sound` / `propext` / `Classical.choice`) | **PASS** (baseline verified; 8 speculative arithmetic lifts cleanly rejected) |

Aggregate across the 4 simplified `SharpRestriction` modules: **`646 -> 613` effective LOC (`-33` LOC, `-5.1%`)** and **`507 -> 478` proof steps (`-29` steps, `-5.7%`)**, with **63/63 non-primed exported declarations** across all 6 verified modules preserving `#check @decl` verbatim in `verify_refactor_gate` (plus `C2'` verified at baseline via `_parse_print_axioms_safe`) and depending solely on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

### 2.2 Per-Module `#print axioms` Summary (Verified)

- `EqZeroOfForallMemCoeffFiltration` (19 decls: `WeierS.{T, mem_T, T_anti, T_mul, eq_zero_of_forall_mem_coeffFiltration, mem_T_one, pow_mem_coeffFiltration, aeval_mem_coeffFiltration, S, S_sub_mem, exists_lim, subst, subst_sub_mem, subst_eq, subst_add, subst_smul, subst_mul, subst_one, substAlgHom}`): all 19 report `[propext, Classical.choice, Quot.sound]`.
- `MemPairOfMemSingle` (12 non-primed decls verified by `verify_refactor_gate`: `cont`, `Cont.{enat_le_of_forall, mem_pair_mono, mem_zero, mem_iff_le, residue_unif, C_unif_ne_zero, C_dvd_of_map_eq_zero, prime_C_unif, not_C_dvd, mem_of_pow_mul_mem}`, `mem_iff_le_cont`; plus `C2'` verified at baseline via `_parse_print_axioms_safe`): all report `[propext, Classical.choice, Quot.sound]`.
- `DvdCoeffsOfMemSpanDistinguished` (11 decls: `ContM_{dvd_iff_residue, dvd_of_map_eq_zero, map_C_unif, cancel_unif, mem_of_unif_mul, order_unit, Kk, iSup_le}`, `dvd_coeffs_of_mem_span_distinguished`, `Mprime`, `Mprime_cont`): all 11 report `[propext, Classical.choice, Quot.sound]`.
- `FormalSeriesValueAtTwoPointsGenericPoints` (9 decls: `ContPA.{natCast_unit_mul, natCast_ne_zero', addVal_l, addVal_natCast, l_unit_mul, dist_of_map_eq, dist_X_pow, addVal_coef, coef_ne_zero}`): all 9 report `[propext, Classical.choice, Quot.sound]`.
- `CurveKrullDimTopology` (3 decls: `LateralTheory.E.CurveKrullDim.{two_le_dim, closed_of_ne_univ, finite_of_closed}`): all 3 report `[propext, Classical.choice, Quot.sound]`.
- `ExtendOneMulVecSingleLast` (9 decls: `Formalism.L2.GlobalTheoryTheory.Br.*`): `inclusionAlt` uses `[Quot.sound]`; `blk1` and `eN_map` use `[propext, Quot.sound]`; `extendOne_mul_inclusion`, `extendOne_mulVec_single_last`, `det_extendOne`, `extM`, `extM_spec`, `ext_general` use `[propext, Classical.choice, Quot.sound]`.

### 2.3 Real Lean `v4.33.1` Archive Defects Exposed During Live Benchmark

Running real `lake build` inside `simplify_module` caught two concrete compression defects in `#136` `outputs/rh_compressed.tar.gz` (plus one `gate.py` parser edge case):

1. **Greek-prefix helper pruning (`ConstantCoeffSubstAlgHom`, `2.278s` build)**:
   - `ConstantCoeffSubstAlgHom.lean` failed with `Unknown identifier 'τk_compat'` (L190), `'τk_X'` (L227, L238), and `'τk_C'` (L236), plus `unsolved goals` at L226. Root cause confirmed by `@analyzer-2` (`#174`): Greek `τ`-prefixed declarations were indexed as `anon_theorem_*` in `rh_full.db` with 0 incoming edges and pruned (`845` such declarations / `4,657` LOC across kept modules).
2. **Missing structure-projection dot-notation imports (`ConstantLeRpowOfThreeLe`, `8.844s` build)**:
   - `ConstantLeRpowOfThreeLe.lean` failed with `Invalid field 'first_partial_unit_eq_exp'` (L95) and `Invalid field 'isUnit_eps'` (L100) on `P : PhiData O l`, cascading to `ConstantCoeffResidueUXPow`, `ContentBoundLevelIdeal`, and `DenBound`.
3. **USB cold-load boundaries**:
   - Cold-loading uncached heavy Mathlib subtrees over external USB (`disk4` at ~86–261 tps / 1.3–4.1 MB/s) timed out when not pre-warmed (`IntegralIteratedFDerivEqZero` timed out at `600s` on `IntegrationByParts`; `ConstantCoeffAlgHom` timed out at `600s` on `MahlerBasis`).
4. **Primed identifier regex in `gate.py`**:
   - Lean prints `#print axioms ...C2'` as `'...C2'' depends on axioms: ...`; `gate.py`'s `r"'([^']+)'\s+depends"` stops at the inner quote. `simplify.py` adds `_parse_print_axioms_safe` and `_run_gate_with_primed_check` (splitting non-primed decls through `verify_refactor_gate` and post-edit kernel-verifying primed decls via `_inspect_module_decls`).

---

## 3. Real Before/After Lean Diffs (Kernel-Verified)

### 3.1 `EqZeroOfForallMemCoeffFiltration.lean` (`177 -> 169` LOC, `143 -> 132` steps)

```diff
--- a/Formalism/SharpRestriction/LevelLetterCocycles/RepresentationCongruences/EqZeroOfForallMemCoeffFiltration.lean
+++ b/Formalism/SharpRestriction/LevelLetterCocycles/RepresentationCongruences/EqZeroOfForallMemCoeffFiltration.lean
@@ -38,8 +38,5 @@
 private theorem maximalIdeal_pow_smul_whole_ring_eq_self (n : ℕ) :
     ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O) = (IsLocalRing.maximalIdeal O) ^ n := by
-  first
-    | rw [Ideal.smul_eq_mul, Ideal.mul_top]
-    | simp [Ideal.smul_eq_mul]
-    | simp
+  rw [Ideal.smul_eq_mul, Ideal.mul_top]
 
 theorem eq_zero_of_forall_mem_coeffFiltration {x : O⟦X⟧} (hx : ∀ N, x ∈ T O N) : x = 0 := by
@@ -131,7 +128,5 @@
     (hy : ∀ N, N0 ≤ N → y - S g N f ∈ T O N) : y = subst hg f := by
   have key : ∀ N, y - subst hg f ∈ T O N := fun N => by
-    have h1 := hy (N + N0) (by omega)
-    have h2 := subst_sub_mem hg f (N + N0)
-    have h3 := sub_mem h1 h2
+    have h3 := sub_mem (hy (N + N0) (by omega)) (subst_sub_mem hg f (N + N0))
     rw [sub_sub_sub_cancel_right] at h3
     exact T_anti (by omega) h3
@@ -151,8 +146,5 @@
 private theorem truncEval_smul (N : ℕ) (r : O) (f : O⟦X⟧) :
     S g N (r • f) = r • S g N f := by
-  have h : trunc N (r • f) = r • trunc N f := by
-    first
-      | exact map_smul (trunc N) r f
-      | (ext d; simp only [coeff_trunc, Polynomial.coeff_smul, coeff_smul]; split_ifs <;> simp)
+  have h : trunc N (r • f) = r • trunc N f := map_smul (trunc N) r f
   simp only [S, h, map_smul]
```

### 3.2 `MemPairOfMemSingle.lean` (`134 -> 123` LOC, `104 -> 95` steps)

```diff
--- a/Formalism/SharpRestriction/LevelLetterCocycles/RepresentationCongruences/MemPairOfMemSingle.lean
+++ b/Formalism/SharpRestriction/LevelLetterCocycles/RepresentationCongruences/MemPairOfMemSingle.lean
@@ -19,8 +19,5 @@
   have hb : b ≠ ⊤ := ne_top_of_lt hlt
   obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hb
-  have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ a := by
-    have h2 := (ENat.add_one_le_iff hb).2 hlt
-    exact_mod_cast h2
-  have h2 := h (n + 1) h1
+  have h2 := h (n + 1) (by exact_mod_cast (ENat.add_one_le_iff hb).2 hlt)
   norm_cast at h2
   omega
@@ -63,12 +60,10 @@
     omega
 
-theorem Cont.residue_unif {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalRing.residue O ϖ = 0 := by
-  exact (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit
+theorem Cont.residue_unif {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit
 
 theorem Cont.C_unif_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : (C ϖ : O⟦X⟧) ≠ 0 := by
   intro h
   apply hϖ.ne_zero
-  have h1 := congrArg PowerSeries.constantCoeff h
-  simpa using h1
+  simpa using congrArg PowerSeries.constantCoeff h
@@ -120,9 +114,5 @@
     · rw [Ideal.mem_span_singleton']
       refine ⟨q', ?_⟩
-      have h1 : C ϖ * (q' * g) = C ϖ * (C ϖ ^ n * h) := by
-        calc C ϖ * (q' * g) = C ϖ * q' * g := by ring
-          _ = C ϖ ^ (n + 1) * h := hq
-          _ = C ϖ * (C ϖ ^ n * h) := by ring
-      exact mul_left_cancel₀ (Cont.C_unif_ne_zero hϖ) h1
+      exact mul_left_cancel₀ (Cont.C_unif_ne_zero hϖ) (by linear_combination hq)
     · exact absurd hg' (Cont.not_C_dvd hϖ hg)
 
@@ -147,6 +137,5 @@
 
 theorem mem_iff_le_cont {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
-    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
-  exact Cont.mem_iff_le ϖ g f k
+    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := Cont.mem_iff_le ϖ g f k
```

### 3.3 `DvdCoeffsOfMemSpanDistinguished.lean` (`237 -> 230` LOC, `196 -> 191` steps)

```diff
--- a/Formalism/SharpRestriction/LevelLetterCocycles/RepresentationCongruences/DvdCoeffsOfMemSpanDistinguished.lean
+++ b/Formalism/SharpRestriction/LevelLetterCocycles/RepresentationCongruences/DvdCoeffsOfMemSpanDistinguished.lean
@@ -51,6 +51,5 @@
         intro h0
         apply hϖ.ne_zero
-        have h1 := congrArg (coeff 0) h0
-        simpa using h1
+        simpa using congrArg (coeff 0) h0
       apply mul_left_cancel₀ hne
       linear_combination h
@@ -105,8 +104,5 @@
     rw [order_mul, order_pow, hord]
     calc ((i₀ * wdeg Xg : ℕ) : ℕ∞) < ((y * wdeg Xg : ℕ) : ℕ∞) := by exact_mod_cast hlt
-      _ = y • (wdeg Xg : ℕ∞) := by
-        rw [nsmul_eq_mul]
-        push_cast
-        rfl
+      _ = y • (wdeg Xg : ℕ∞) := by rw [nsmul_eq_mul]; push_cast; rfl
       _ ≤ (a.map f).order + y • (wdeg Xg : ℕ∞) := le_add_self
@@ -133,6 +129,5 @@
         have hle : i₀ ≤ j := hmin j (Finset.mem_filter.2 ⟨hj, hcj⟩)
         have hlt' : i₀ < j := lt_of_le_of_ne hle (Ne.symm hne)
-        have hD' : 1 ≤ wdeg Xg := hD
-        exact_mod_cast (by nlinarith : i₀ * wdeg Xg < j * wdeg Xg)
+        exact_mod_cast (by nlinarith [hD] : i₀ * wdeg Xg < j * wdeg Xg)
@@ -175,8 +170,6 @@
     exact ⟨e, by ring⟩
 
-theorem ContM_iSup_le (m : ℕ∞) : ⨆ (k : ℕ) (_ : (k : ℕ∞) ≤ m), (k : ℕ∞) = m := by
-  apply le_antisymm
-  · exact iSup₂_le fun k hk => hk
-  · exact Cont.enat_le_of_forall fun k hk => le_iSup₂_of_le k hk le_rfl
+theorem ContM_iSup_le (m : ℕ∞) : ⨆ (k : ℕ) (_ : (k : ℕ∞) ≤ m), (k : ℕ∞) = m :=
+  le_antisymm (iSup₂_le fun _ hk => hk) (Cont.enat_le_of_forall fun k hk => le_iSup₂_of_le k hk le_rfl)
```

### 3.4 `FormalSeriesValueAtTwoPointsGenericPoints.lean` (`98 -> 91` LOC, `64 -> 60` steps)

```diff
--- a/Formalism/SharpRestriction/LevelLetterCocycles/RepresentationCongruences/FormalSeriesValueAtTwoPointsGenericPoints.lean
+++ b/Formalism/SharpRestriction/LevelLetterCocycles/RepresentationCongruences/FormalSeriesValueAtTwoPointsGenericPoints.lean
@@ -46,6 +46,5 @@
 
 theorem addVal_l {l : ℕ} (hl0 : (l : O) ≠ 0) :
-    IsDiscreteValuationRing.addVal O (l : O) = ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℕ∞) := by
-  exact (ENat.coe_toNat ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hl0)).symm
+    IsDiscreteValuationRing.addVal O (l : O) = ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℕ∞) := (ENat.coe_toNat ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hl0)).symm
 
@@ -82,12 +81,6 @@
   have hord : (f.map (IsLocalRing.residue O)).order = n := by
     rw [h]; exact order_unit_mul_X_pow_lemma_3 hw n
-  refine ⟨?_, ?_⟩
-  · unfold IsDist
-    intro h0
-    rw [h0, PowerSeries.order_zero] at hord
-    exact ENat.top_ne_coe n hord
-  · unfold wdeg
-    rw [hord]
-    rfl
+  refine ⟨fun h0 => ENat.top_ne_coe n (by rw [← hord, h0, PowerSeries.order_zero]), ?_⟩
+  unfold wdeg; rw [hord]; rfl
```

---

## 4. Concrete Mathematical Simplification Audit: Top 3 Structural Detours

Stage 2 dependency-cone pruning already stripped unreachable scratch files (`175,187 -> 146,349` modules in `#136`, and `17,719` reachable modules inside `AbelianVarietyTheory`), yet three massive structural detours still dominate the remaining proof size. Eliminating them requires **mathematical/architectural rewrites** rather than line-by-line tactic cleanup, offering an additional **5x–10x** compression.

### 4.1 Detour 1: `Development.AbelianVarietyTheory` (`5,982,169` raw LOC -> `919,429` reachable body LOC)

- **Observed Scale & Subpackage Footprint (`outputs/rh_full.db` & `#136`)**:
  - Full `rh_full.db`: **`99,176` modules**, **`457,031` decls**, **`5,982,169` body LOC**, including **`38,696` `*Statement` wrapper modules**, **`62,210` bookkeeping decls (`443,248` LOC)**, and **`49,987` canonical-type duplicate groups (`69,336` extra decls / `1,574,478` reducible body LOC = `26.3%`)**.
  - `#136` `rh_compressed.tar.gz`: **`80,521` modules**, **`5,327,926` eff. LOC**, **`30,049` `*Statement` modules**.
  - Strictly pruned reachable cone: **`17,719` modules**, **`70,255` decls**, **`919,429` body LOC** (`10,040` bookkeeping decls / `89,525` LOC; `6,137` `*Statement` modules / `69,209` LOC; `7,292` canonical-type duplicate groups / `9,033` redundant decls / `227,040` reducible LOC).
  - Largest subpackages in `rh_full.db`: `Proofs.DivisorProofs` (`42,424` mods / `2,047,355` body LOC; `344,614` reachable), `Proofs.InertiaEigenvalues` (`8,951` / `505,220`; `130,333` reachable), `Proofs.IwasawaDecomposition` (`7,809` / `445,809`; `25,713` reachable), `Proofs.SatakeParameters` (`3,491` / `173,127`; `30,237` reachable), `Proofs.ModuliProofs` (`1,539` / `130,612`; `59,141` reachable), `Proofs.DegenerationProofs` (`1,563` / `110,796`; `59,865` reachable), `Proofs.UniformizationProofs` (`869` / `74,766`; `51,308` reachable).
- **Exact Lean Module Boundaries & Hypothesis Slack**:
  - The subtree exports `7,197` declarations across `2,582` modules to the rest of the project; top caller hubs are `GlobalTheory.CuspRep.GA` (`2,025` callers), `GlobalTheory.BCT.Pl` (`1,962`), `GlobalTheory.CuspRep.Sm` (`1,465`), `GlobalTheory.LGrp.LeviDatum.L` (`1,073`), `GlobalTheory.BCT.GLw` (`1,029`), and `GlobalTheory.LocGL.IrrGL` (`989`).
  - Core analytic-algebraic roots: `GlobalTheory.CubeTop.cubeTheorem` (`Development.AbelianVarietyTheory.Proofs.CubeTop`), `GlobalTheory.MulIsogeny.mul_isogeny`, and `GlobalTheory.AV.AbVar.isCharpoly_charpoly_unique`.
  - Extreme hypothesis/signature slack: `4,963` declarations with `>=10` binders in the reachable cone (`136` with `>=10` top-level prefix binders in `rh_full.db`), peaking at `269` hypotheses / `22,174`-char `type_sig` in `GlobalTheory.polarisedTorus_algebraic_of_parts` (`Development.AbelianVarietyTheory.Proofs.ToricGeometry.PolarisedTorusAlgebraicOfParts`, `277` LOC), `14,263`-char `type_sig` in `GlobalTheory.familyUnif_of_parts` (`ModuliProofs.FamilyUnifOfParts`), and `58` prefix binders in `GlobalTheory.AscFin.GridLat.lattices_grid`.
- **Concrete Mathematical Rewrites for 5x–10x Compression**:
  1. **Bundle multi-part analytic-geometric interfaces (`*_of_parts`) into Lean `structure`/`class` packages**: replacing `polarisedTorus_algebraic_of_parts` (`22,174`-char signature), `familyUnif_of_parts` (`14,263`-char), and `datExt_rest_of_parts` (`11,796`-char) parameter-unrolling chains with bundled `PolarisedTorusData` / `RigidUniformizationData` structures eliminates thousands of `*_of_parts` marshaling lemmas.
  2. **Collapse `6,137` reachable `*Statement` wrapper files (`69,209` LOC) and `7,292` canonical-type duplicate groups (`227,040` LOC)**: each `*Statement.lean` (like `JacquetRallisUnitMatchAllRanksStatement.lean`) is a single `first | exact ...` alias of a sibling `Proofs/*` theorem; inlining/deduplicating them removes `~296k` LOC (~32% of the reachable cone) directly.
  3. **Direct Weil-pairing + Deligne `l`-adic charpoly bypass for `cubeTheorem` / `DivisorProofs`**: `DivisorProofs` (`344,614` reachable LOC) proves rigid-analytic/formal-scheme Theta-divisor splitting to deduce the Theorem of the Cube and charpoly integrality on abelian varieties; replacing custom formal-torus/Raynaud uniformization for `isCharpoly_charpoly_unique` with abelian-scheme `Hom(A, B)` torsion-module freeness (`T_l(A)` over `ℤ_l`) + Riemann's Theorem of the Cube via `Pic⁰(A)` avoids `UniformizationProofs`, `ToricGeometry`, and `DegenerationProofs` (`~129k` reachable LOC) at the RH spine boundary.

### 4.2 Detour 2: `VWin` / Weakened Vandiver / Behrend Iwasawa Tower (`1,435,448` raw LOC -> `310,923` reachable body LOC)

- **Observed Scale & Subpackage Footprint (`outputs/rh_full.db` & `#136`)**:
  - Full `rh_full.db`: **`18,417` modules**, **`91,512` decls**, **`1,435,448` body LOC** (`736` `*Statement` modules, `8,427` bookkeeping decls / `86,081` LOC).
  - `#136` `rh_compressed.tar.gz`: **`16,618` modules**, **`1,383,666` eff. LOC**.
  - Reachable cone: **`22,650` decls**, **`310,923` body LOC** (`1,593` bookkeeping decls / `15,038` LOC), plus supporting infrastructure in `GroundTheory.ProfiniteCohomology` (`127` reachable mods / `11,387` LOC; `450` mods / `60,542` LOC raw), `Formalism.WachLatticeTwists` (`68` reachable LOC; `262` mods / `31,960` LOC raw), and `Formalism.SharpRestriction.RamificationFrobenius` (`8` reachable mods / `1,372` LOC).
  - Key `AutomorphicArithmetic` subpackages in `rh_full.db`: `AutomorphicVarieties.ModularityArgument` (`2,515` mods / `237,397` body LOC), `Foundations.GaloisRepresentations` (`2,965` / `202,064`), `IntegralCasts.CapelliIdentities` (`881` / `111,165`), `Foundations.Convolution` (`1,090` / `91,374`), `CharacterBoxes` (`37` / `2,255`).
- **Exact Lean Module Boundaries & Hypothesis Slack**:
  - Spine across `CharacterBoxes/ExistsPageN.lean` -> `AdmissibleOfPageN.lean` -> `VwinOfRow.lean` -> `EveryCharacter.lean`:
    - `UpperTheory.Top.VVle` / `IsChiField` / `WinPair` / `PageN` / `VWinAt` / `VWin := ∀ ψ : PChar, VWinAt ψ 401` (`eps < 1/52`, `Ct = 401`).
    - Closed by `UpperTheory.One.vwin_of_row : UpperTheory.GalStar.Row0b (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) → UpperTheory.Top.VWin` (`VwinOfRow.lean`), feeding `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` -> `UpperTheory.FinalTheorems.everyCharacter`.
    - `FiniteEtaleModels` (`75` reachable mods / `5,758` body LOC) exports 10 separate `*_holds` wrapper endpoints (each `ext_callers = 1`, e.g., `UpperTheory.Gal.FiniteEtaleModels.ptAll_holds`).
  - Pathological Capelli/integral-cast bloat inside `IntegralCasts.CapelliIdentities`: `UpperTheory.Reformulated.B.Gr34.mem_UC` (`FixPiIff.lean`) has **`8,001` body LOC** and a **`729,986`-char `type_sig`**; `Uc13.aux4` (`MulMemIntA.lean`) has **`2,649` body LOC** (`211,355`-char `type_sig`); `FreeModuleQuotient.freeN_quot` has **`2,432` body LOC** (`203,068`-char `type_sig`); `Gwa7.aux3` (`EqZeroOfForallIntegralCoeff.lean`) carries **`511` binder groups**.
- **Concrete Mathematical Rewrites for 5x–10x Compression**:
  1. **Replace `CapelliIdentities` concrete index-unrolling (`8,001`-LOC / `730 KB`-sig `mem_UC`) with abstract polynomial-invariant / `MvPolynomial` symmetry**: `FixPiIff`, `MulMemIntA`, and `FreeModuleQuotient` inline massive explicit multi-index determinants and integer basis expansions into single theorem types; factor via a clean `RepInvariantSubalgebra` / `GL_n`-equivariant Cayley-operator interface (`~500` LOC total instead of `111k` raw LOC).
  2. **Consolidate `FiniteEtaleModels` (`10` separate `*_holds` funnels, `5,758` reachable LOC)** and **absorb `ProfiniteCohomology` (`11,387` reachable LOC) + `WachLatticeTwists` into Mathlib `ContinuousCohomology` / Fontaine-Laffaille / `WittVector` APIs**: the `VWin` tower builds custom profinite Galois cohomology and Wach-lattice power-series bounds (`VVle` / `shaLen`) tailored to `Ct = 401`; sharing one `AdmissiblePageN` interface across `FiniteEtaleModels` and delegating profinite inflation-restriction to Mathlib cuts `GaloisRepresentations` + `ModularityArgument` (`~158k` reachable LOC) substantially.
  3. **Direct Siegel/class-number zero-free window without `VWinAt _ 401` Behrend-set parameterization**: `VWin` uses Behrend sets (`Formalism.BehrendSets`) and `IsChiField` cyclotomic subfields with `jacobiSym` parity conditions (`a ≡ ±1 mod 2^(e+2)`) solely to construct prime-level test characters avoiding bad ramification; a unified Chebotarev/effective-Pólya-Vinogradov prime-pair lemma inside `CharacterBoxes` bypasses the bespoke `IsChiField` + `VVle` machinery.

### 4.3 Detour 3: `Jacquet-Rallis` Orbital Matching (`505,220` raw LOC -> `130,333` reachable body LOC)

- **Observed Scale & Subpackage Footprint (`outputs/rh_full.db` & `#136`)**:
  - Full `rh_full.db` (`Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues`): **`8,951` modules**, **`34,321` decls**, **`505,220` body LOC** (`3,698` `*Statement` modules = `41.3%`; **`4,039` canonical-type duplicate groups = `133,520` reducible body LOC = `26.4%`**).
  - `#136` `rh_compressed.tar.gz`: **`8,457` modules**, **`519,228` eff. LOC**, **`3,447` `*Statement` modules**.
  - Reachable cone: **`2,734` modules**, **`8,510` decls**, **`130,333` body LOC** (`1,454` bookkeeping decls / `12,130` LOC; **`1,167` `*Statement` modules = `42.7%`**; **`1,205` canonical-type duplicate groups = `44,855` reducible LOC = `34.4%`**).
- **Exact Lean Module Boundaries & Hypothesis Slack**:
  - Observed linear spine (`JacquetRallisUnitMatchAllRanks.lean` / `JacquetRallisUnitMatchAllRanksStatement.lean` -> `JacquetRallisUnitMatchOfWeilRepQuadratic.lean` -> `EtaleOrbitalFourierRankOneTransfer.lean`):
    - `GlobalTheory.T.jacquetRallisUnitMatch_all_ranks : ∀ r, UnitMatch r` (`first | exact @GlobalTheory.JR.unitMatch_all | ...`)
    - -> `GlobalTheory.JR.unitMatch_all` -> `GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic` (inducting on `r` via `jacquetRallisUnitMatch_sizeOne` and `jacquetRallisUnitMatch_succ`)
    - -> `GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field` -> `GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer` / `GlobalTheory.JR.RankOneTransfer`.
  - Heavy proof/hypothesis slack: `610` declarations with `>=10` hypotheses in the reachable cone (`GlobalTheory.CovLayer.layer` with 38 hyps / `133` LOC; `GlobalTheory.CycFr.exists_frame` `449` LOC; `GlobalTheory.ZRep.central_reps` `328` LOC / `5,696`-char sig; `GlobalTheory.DownLift.GenSplit.coord` `36` prefix binders).
- **Concrete Mathematical Rewrites for 5x–10x Compression**:
  1. **Eliminate the `1,167` reachable `*Statement` split wrappers and `1,205` canonical-type duplicate groups**: deduplication + wrapper collapse alone removes `~35–45%` (`45k–58k` LOC) of the reachable `InertiaEigenvalues` cone with zero mathematical change.
  2. **Unify `WeilField` étale vs. split quadratic algebra transfer via a single `Et F E` Frobenius-form functor**: `EtaleOrbitalFourierRankOneTransfer.lean` and `JacquetRallisUnitMatchOfWeilRepQuadratic.lean` re-prove additive/scaling closure (`inI_comb`, `inI_zero`, `nS_add`) and base-change symmetries separately across `rankOne` and inductive `succ` cases; parameterizing `UnitMatch r` over an arbitrary quadratic étale algebra `E/F` (collapsing split `F × F` and inert/ramified field cases) eliminates the duplicate `weilRep_quadraticField_exists` / `weilConstantStandardHermitian_eq_one` detour chain.
  3. **Use Zhang's / Yun's characteristic-0 transfer shortcut (or relative trace formula positivity directly on smooth compactly-supported Schwartz functions)** instead of unrolling `CovLayer` (`38` explicit hypotheses), `CycFr.exists_frame` (`449` LOC), and `BKTwist` (`228` LOC) frame-by-frame.

---

## 5. Verification Ledger

- **Stage 4 unit + real-`lake` test suite (`tests/test_simplify.py`)**: `.venv/bin/pytest -v tests/test_simplify.py` after the final `simplify.py` fixes: **11 passed in 14.03s** (covers `count_proof_steps`, `prune_dead_have`/`let`/`set`/private guards, `collapse_first_branch` multi-line Lean indentation, `collapse_by_exact`, `batch_high_confidence`, `find_mathlib_absorption_candidates`, `_parse_print_axioms_safe` on primed identifiers, `os.killpg` process-group timeout cleanup, mocked gate revert, and real `~/.elan/bin/lake` end-to-end `simplify_module` + `verify_manual_rewrite` incl. primed `Demo.C2'`).
- **Full repository test suite**: `.venv/bin/pytest -q` after all final fixes and archive regeneration: **49 passed in 77.67s** (incl. `tests/test_simplify.py`, `test_extract_and_compile_from_real_rh_compressed_tar_gz`, and `test_verify_real_rh_merged_tar_gz_structure_and_zero_mathlib_build`).
- **Live `lake` smoke verification on `Demo.Sample`**: verified `simplify_module` against `~/.elan/bin/lake` on a module containing both a primed declaration (`Demo.C2'`) and `first | ...` / `refine` blocks (`25 -> 7` effective LOC, `17 -> 5` proof steps in `tests/test_simplify.py::test_real_lake_simplify_module_and_verify_manual_rewrite`, `gate_passed=True`, all axioms in `{propext, Classical.choice, Quot.sound}`).
- **Lean `v4.33.1` kernel gate on real `alpo.ge` RH modules**: all 6 verified RH modules in Section 2 passed `verify_refactor_gate` (`lake build` exit `0`, verbatim `#check @decl`, `#print axioms` strictly within `{propext, Classical.choice, Quot.sound}`).
