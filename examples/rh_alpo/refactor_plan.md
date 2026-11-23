# Kernel-Checked Refactoring Plan

Total selected work orders: **20**

| # | Target | Scope | Internal LOC | Interface Width | Est. Savings | Priority | Rationale |
|---:|---|---|---:|---:|---:|---:|---|
| 1 | `Development / Abelian Variety Theory: se Good` | cluster | 4,621,552 | 500 | 1,461,267 | 3409898.1 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 2 | `Development / Automorphic Arithmetic: zel` | cluster | 1,262,695 | 500 | 189,404 | 647863.2 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 3 | `Development / Automorphic Spectrum: whit Heredity` | cluster | 775,345 | 500 | 210,751 | 522549.5 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 4 | `Development / Weil Bound: segment Representation` | cluster | 612,767 | 500 | 91,915 | 287487.4 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 5 | `Formalism: gluing mass holds` | cluster | 564,142 | 500 | 84,621 | 270547.6 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 6 | `Formalism: inert conditions hold` | cluster | 428,351 | 500 | 64,252 | 199670.0 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 7 | `Formalism: lattice average induction` | cluster | 310,929 | 500 | 46,639 | 153437.2 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 8 | `Formalism / Period Integrals: row lattice mass` | cluster | 273,269 | 500 | 42,802 | 141004.9 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 9 | `Reciprocity Theory: weight Indep` | cluster | 273,303 | 500 | 40,995 | 132710.9 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 10 | `Ground Theory / Heights And Theta: power Sum Hom injective` | cluster | 252,201 | 500 | 37,830 | 130487.9 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 11 | `Companion Theory / Spectral Geometry: reduce` | cluster | 82,589 | 500 | 25,278 | 59059.1 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 12 | `Development / Resolution Of Singularities: functorial Resolution Char Zero` | cluster | 116,064 | 161 | 17,409 | 48780.9 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 13 | `Development / Etale Cohomology: ker Loc of` | cluster | 73,462 | 500 | 12,718 | 41346.0 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 14 | `Ground Theory / Automorphic Forms: exists reduced` | cluster | 91,329 | 500 | 13,699 | 33717.0 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 15 | `Ground Theory / Profinite Cohomology` | cluster | 53,363 | 500 | 8,004 | 20325.8 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 16 | `Formalism: theorem MV7` | cluster | 38,869 | 500 | 5,875 | 19723.3 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 17 | `Formalism / GL3 Mean Squares: li Stat` | cluster | 44,498 | 400 | 6,674 | 18520.9 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 18 | `Companion Theory / Automorphic Theory: is Closed unit Ball` | cluster | 31,401 | 500 | 4,771 | 16284.9 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 19 | `Ground Theory: discrete Topology principal Subgroup` | cluster | 43,787 | 500 | 6,568 | 16154.6 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 20 | `Positivity Theory / Automorphic Forms: integral plus` | cluster | 31,232 | 500 | 4,684 | 14938.2 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |

## Work Order 1: `Development / Abelian Variety Theory: se Good` (`cluster-34`)

- **Internal LOC:** 4,621,552 (337931 declarations; bookkeeping ratio 13.4%)
- **Formal Interface Width:** 500 (leverage ratio 9243.1 LOC/item)
- **Estimated Savings:** ~1,461,267 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.BasicNotions.D7`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp`, `Formalism.BasicNotions.TH.HSp`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host`, `ReciprocityTheory.ChartRestriction.G.Semi.LB`, `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum`
- **Outputs (must preserve exactly):** `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE`, `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc`, `GlobalTheory.CuspRep.GA`, `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base`, `GlobalTheory.BCT.Pl`, `GlobalTheory.Serre.Lie.map_mul`, `GlobalTheory.CuspRep.Sm`, `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.HomExtendsOverDVR Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.LevelStructureForms Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.MultiplicationEtaleTorsion` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 4621552 LOC)

## Work Order 2: `Development / Automorphic Arithmetic: zel` (`cluster-52`)

- **Internal LOC:** 1,262,695 (78545 declarations; bookkeeping ratio 8.9%)
- **Formal Interface Width:** 500 (leverage ratio 2525.39 LOC/item)
- **Estimated Savings:** ~189,404 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `Formalism.BasicNotions.D7`, `Formalism.HC.HostRaw.F`, `GlobalTheory.Serre.Lie.map_mul`, `Formalism.BasicNotions.Ranks.n`, `Formalism.BasicNotions.SizeData₂`, `Formalism.MainNotions.GL3Theta.G1.l`, `GlobalTheory.Mem.Base.O`
- **Outputs (must preserve exactly):** `Formalism.ConjugateSelfDual.G`, `Formalism.ConjugateSelfDual.IsPlaceOver`, `Formalism.ConjugateSelfDual.Qbar`, `Formalism.ConjugateSelfDual.normV`, `Reformulated.AutPerF.BdRPlus.eval`, `UpperTheory.V.HV.Coef`, `Reformulated.AutPerF.Tilt.coeff_map`, `Reformulated.AutPerF.Acris.eval`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.AutomorphicArithmetic.AdelicGluing.BaseChangeLevelIsOpenIsCompactContainsIwahori Development.AutomorphicArithmetic.AdelicGluing.CommuteHeckeOperatorFiniteConvolutionOfFreeIndic Development.AutomorphicArithmetic.AdelicGluing.CuspidalProjectionCcStarTensIsLeftSmooth` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 1262695 LOC)

## Work Order 3: `Development / Automorphic Spectrum: whit Heredity` (`cluster-33`)

- **Internal LOC:** 775,345 (57403 declarations; bookkeeping ratio 13.0%)
- **Formal Interface Width:** 500 (leverage ratio 1550.69 LOC/item)
- **Estimated Savings:** ~210,751 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host`, `Formalism.BasicNotions.D7`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff`
- **Outputs (must preserve exactly):** `GlobalTheory.CompanionTheory.Ar.Cpt`, `GlobalTheory.CompanionTheory.Ar.genPt`, `GlobalTheory.CompanionTheory.Ar.LieModel`, `GlobalTheory.CompanionTheory.Ar.centre`, `GlobalTheory.CompanionTheory.Ar.HodgeCpt`, `GlobalTheory.CompanionTheory.Ar.LieEx.hom`, `GlobalTheory.CompanionTheory.Ar.CMType`, `GlobalTheory.CompanionTheory.Ar.regAt`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes Development.AutomorphicSpectrum.Definitions.AdelicLattices.IsSelfDualLat Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 775345 LOC)

## Work Order 4: `Development / Weil Bound: segment Representation` (`cluster-32`)

- **Internal LOC:** 612,767 (50371 declarations; bookkeeping ratio 8.0%)
- **Formal Interface Width:** 500 (leverage ratio 1225.53 LOC/item)
- **Estimated Savings:** ~91,915 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF`, `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc`, `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp`, `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base`, `Formalism.BasicNotions.D7`, `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`
- **Outputs (must preserve exactly):** `PositivityTheory.RgTw.Mat`, `PositivityTheory.RgBcC.GLs`, `PositivityTheory.Rg.Tf.Core.G1`, `GlobalTheory.BZMir.Mir`, `CrystallineSemistableComparison.CH.CxF.obj`, `CrystallineSemistableComparison.CH.Mor.hom`, `CrystallineSemistableComparison.PAlg`, `CrystallineSemistableComparison.Pb.IdF`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.WeilBound.CoreStatements.AbelianDeRhamStructure.AbelianDeRhamPages.AbelianDeRhamStructureOfPage Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.AbelianDeRhamPage Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.Bridge` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 612767 LOC)

## Work Order 5: `Formalism: gluing mass holds` (`cluster-105`)

- **Internal LOC:** 564,142 (53880 declarations; bookkeeping ratio 10.4%)
- **Formal Interface Width:** 500 (leverage ratio 1128.28 LOC/item)
- **Estimated Savings:** ~84,621 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.BasicNotions.D7`, `Formalism.BasicNotions.DivData.R`, `Formalism.MainNotions.S.Loc.Model.R`, `Formalism.MainNotions.S.VS`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `Formalism.MainNotions.S.TopsChoicePartA.Lev.B`, `Formalism.MainNotions.S.Loc.Model`, `Formalism.BasicNotions.Scale.L`
- **Outputs (must preserve exactly):** `Formalism.L2.Theta.GA`, `Formalism.L2.Theta.AE`, `Formalism.IndefR.Datum.WO`, `Formalism.L2.GlobalTheoryTheory.Arith.host`, `Formalism.L2.Indef.Examples₂.one.what₂`, `Formalism.L2.Indef.Examples₂.two.what₂`, `Formalism.IndefR.Datum.InfFam`, `Formalism.L2.DIV.Pl`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries Formalism.ArtinHasse.Statement Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.CoeffFrobOfNotDvd` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 564142 LOC)

## Work Order 6: `Formalism: inert conditions hold` (`cluster-103`)

- **Internal LOC:** 428,351 (36930 declarations; bookkeeping ratio 8.4%)
- **Formal Interface Width:** 500 (leverage ratio 856.7 LOC/item)
- **Estimated Savings:** ~64,252 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.BasicNotions.D7`, `Formalism.WeaklyAdmissibleFiltrations.PeriodData`, `Formalism.BasicNotions.DivData.R`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `Formalism.BasicNotions.SizeData₂`, `Formalism.BasicNotions.Ranks.N`, `Formalism.WachCohomologyFacts.Base.p`, `Formalism.BasicNotions.Scale.L`
- **Outputs (must preserve exactly):** `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF`, `Formalism.BasicNotions.LocWach.X`, `Formalism.MainNotions.S.Loc.Model.R`, `Formalism.HC.HostRaw.F`, `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv`, `Formalism.MainNotions.G.Level.M`, `Formalism.MainNotions.S.RowsAut.D`, `Formalism.MainNotions.G.Levels.comp`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.GaussIdealIdentity.GaussIdealPrimality.GaussLocalizationLengthHolds Formalism.GaussIdealIdentity.StatementLA Formalism.SharpRestriction.AdmissibleParameterJoins` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 428351 LOC)

## Work Order 7: `Formalism: lattice average induction` (`cluster-102`)

- **Internal LOC:** 310,929 (29081 declarations; bookkeeping ratio 7.9%)
- **Formal Interface Width:** 500 (leverage ratio 621.86 LOC/item)
- **Estimated Savings:** ~46,639 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.QuantumDeterminants.Hpk`, `Formalism.QuantumDeterminants.Mt`, `Formalism.QuantumDeterminants.herm`, `Formalism.QuantumDeterminants.inWb`, `Formalism.QuantumDeterminants.Tz`, `Formalism.QuantumDeterminants.UWset`, `Formalism.QuantumDeterminants.eI`, `Formalism.QuantumDeterminants.OmX`
- **Outputs (must preserve exactly):** `Formalism.FourierDecayAlt.B.Mat`, `Formalism.FourierDecayAlt.Sz.SizeData.n`, `Formalism.FourierDecayAlt.P.Qx2.Good.map_sum`, `Formalism.FourierDecayAlt.Sz.SizeData.m`, `Formalism.FourierDecayAlt.Sz.Glob.m`, `Formalism.FourierDecayAlt.R.LevelData.D`, `Formalism.FourierDecayAlt.B.GV`, `Formalism.FourierDecayAlt.M.Par`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.HermitianCurvature.ActualZetaSmooth Formalism.HermitianCurvature.ArchimedeanUniformConstantsCompactSupport Formalism.HermitianCurvature.BesselNonvanishingReduction` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 310929 LOC)

## Work Order 8: `Formalism / Period Integrals: row lattice mass` (`cluster-104`)

- **Internal LOC:** 273,269 (24468 declarations; bookkeeping ratio 10.8%)
- **Formal Interface Width:** 500 (leverage ratio 546.54 LOC/item)
- **Estimated Savings:** ~42,802 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.BasicNotions.D7`, `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv`, `Formalism.MainNotions.S.AutInst`, `Formalism.L2.SG.HidaSetting.HidaSetting`, `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF`, `Formalism.BasicNotions.DivData.R`, `Formalism.MainNotions.S.Loc.Model.R`, `Formalism.BasicNotions.HSpace`
- **Outputs (must preserve exactly):** `PI.EagonNorthcottZ.hom`, `PI.TailWork.h`, `PI.PrimeLogOverPWork.E`, `PI.TailWork.g`, `PI.LevelKSplit.W.SemiG.Dat.Pi`, `PI.PrimeLogOverPWork.S`, `PI.EagonNorthcottZ.K`, `Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.R`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.PeriodIntegrals.AdBridgeSteps Formalism.PeriodIntegrals.AdCpctDen Formalism.PeriodIntegrals.AdIndexEq` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 273269 LOC)

## Work Order 9: `Reciprocity Theory: weight Indep` (`cluster-26`)

- **Internal LOC:** 273,303 (21652 declarations; bookkeeping ratio 12.0%)
- **Formal Interface Width:** 500 (leverage ratio 546.61 LOC/item)
- **Estimated Savings:** ~40,995 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.FourierDecayAlt.B.Mat`, `ReciprocityTheory.L2DbarEstimates.V`, `Formalism.BasicNotions.Scale.L`, `Formalism.QuantumDeterminants.Hpk`, `Formalism.FourierDecayAlt.B.GV`, `Formalism.REAL.UJ`, `Formalism.CoboundaryTransfers.Hom.comp`, `Formalism.MainNotions.S.umat`
- **Outputs (must preserve exactly):** `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum`, `ReciprocityTheory.ChartRestriction.G.Semi.LB`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Lemmata.CurryModusPonens.CurryMp Lemmata.FirstBlockLemmaA.Imports Lemmata.FirstBlockLemmaB.Imports` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 273303 LOC)

## Work Order 10: `Ground Theory / Heights And Theta: power Sum Hom injective` (`cluster-28`)

- **Internal LOC:** 252,201 (18280 declarations; bookkeeping ratio 8.5%)
- **Formal Interface Width:** 500 (leverage ratio 504.4 LOC/item)
- **Estimated Savings:** ~37,830 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `ReciprocityTheory.ChartRestriction.G.Geo.MRing`, `ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog`, `ReciprocityTheory.ChartRestriction.G.Geo.MRingOver`, `ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal`, `ReciprocityTheory.ChartRestriction.G.Geo.HermLine`, `ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar`, `ReciprocityTheory.ChartRestriction.G.Geo.mcPts`, `GroundTheory.Automorphic.HermitianForm`
- **Outputs (must preserve exactly):** `GroundTheory.Heights₂.Heights.LowerBoundFree.Line.Ω`, `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg`, `GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentData`, `GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y`, `GroundTheory.Heights₂.Heights.CP.chart`, `GroundTheory.Heights₂.Heights.LowerBoundFree.HodgeData`, `GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentData.n`, `GroundTheory.Heights₂.Heights.LowerBoundFree.Line.L`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Assembly GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 252201 LOC)

## Work Order 11: `Companion Theory / Spectral Geometry: reduce` (`cluster-31`)

- **Internal LOC:** 82,589 (5721 declarations; bookkeeping ratio 14.5%)
- **Formal Interface Width:** 500 (leverage ratio 165.18 LOC/item)
- **Estimated Savings:** ~25,278 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt`, `HeckeCharacterZeroLocus.SiegelWeilU.Fv`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `HeckeCharacterZeroLocus.SiegelWeilU.IsHermND`, `HeckeCharacterZeroLocus.SiegelWeilU.AF`, `CompanionTheory.RgExh.GMod`, `HeckeCharacterZeroLocus.SiegelWeilU.HA`, `HeckeCharacterZeroLocus.SiegelWeilU.HermR`
- **Outputs (must preserve exactly):** `GlobalTheory.CompanionTheory.SW.coordW`, `GlobalTheory.CompanionTheory.SW.IsStdV`, `GlobalTheory.CompanionTheory.SW.coordHerm`, `GlobalTheory.T.tensor_locally_compact_ring`, `GlobalTheory.CompanionTheory.SW.actW`, `GlobalTheory.CompanionTheory.SW.IsLocR`, `GlobalTheory.CompanionTheory.SW.hermScal`, `GlobalTheory.CompanionTheory.SW.IsStdInf`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 82589 LOC)

## Work Order 12: `Development / Resolution Of Singularities: functorial Resolution Char Zero` (`cluster-18`)

- **Internal LOC:** 116,064 (7590 declarations; bookkeeping ratio 10.9%)
- **Formal Interface Width:** 161 (leverage ratio 720.89 LOC/item)
- **Estimated Savings:** ~17,409 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers`
- **Outputs (must preserve exactly):** `FunctorialResolution.BlowupSequence`, `FunctorialResolution.EmbeddedResolution.EtaleChart`, `FunctorialResolution.EmbeddedResolution.EtaleChart.coord`, `FunctorialResolution.HasSimpleNormalCrossings`, `FunctorialResolution.IsPrincipalizingSequence`, `FunctorialResolution.BlowupSequence.structMap`, `FunctorialResolution.EmbeddedResolution.restrictIdeal`, `FunctorialResolution.BlowupSequence.topMap`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.BinaryCoproductBaseChange Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ClopenSubscheme Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.CoproductBaseChange` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 116064 LOC)

## Work Order 13: `Development / Etale Cohomology: ker Loc of` (`cluster-50`)

- **Internal LOC:** 73,462 (9127 declarations; bookkeeping ratio 7.5%)
- **Formal Interface Width:** 500 (leverage ratio 146.92 LOC/item)
- **Estimated Savings:** ~12,718 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GlobalTheory.EtC.Spc`, `GlobalTheory.EtC.Shv`, `GlobalTheory.EtC.Cx`, `GlobalTheory.EtC.Sec`, `GlobalTheory.EtC.SemiMap.op`, `GlobalTheory.EtC.Sec.res`, `GlobalTheory.EtC.tw`, `GlobalTheory.EtC.sch`
- **Outputs (must preserve exactly):** `LateralTheory.E.E4.Sp`, `LateralTheory.EtaleTrace.S`, `LateralTheory.EtaleTrace.V`, `LateralTheory.EtaleTrace.pb`, `LateralTheory.E.EtaleTopologySheaves.SShv`, `LateralTheory.E.E4.pl`, `LateralTheory.CohomologicalPurity.TubeCut.hoc`, `LateralTheory.EtaleTrace.cupV`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.EtaleCohomology.CohomologicalPurity.EtalePurityContinuityOffClosedOfLocalAndChase Development.EtaleCohomology.CohomologicalPurity.FinLeafAW Development.EtaleCohomology.CohomologicalPurity.FinLeafBd` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 73462 LOC)

## Work Order 14: `Ground Theory / Automorphic Forms: exists reduced` (`cluster-48`)

- **Internal LOC:** 91,329 (7970 declarations; bookkeeping ratio 13.8%)
- **Formal Interface Width:** 500 (leverage ratio 182.66 LOC/item)
- **Estimated Savings:** ~13,699 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.Global.integralFiniteAdeles`, `GroundTheory.Global.IdeleGroup`, `GroundTheory.Global.IdeleGroup.ideleModule`, `GroundTheory.LocalField.residueCard`, `GroundTheory.Global.adelicChar`, `GroundTheory.LocalField.modulus`, `GroundTheory.LocalField.selfDualMeasure`, `GroundTheory.Global.homeomorphMixedSpace`
- **Outputs (must preserve exactly):** `GroundTheory.Automorphic.BanachRep.map_mul`, `GroundTheory.Automorphic.BanachRep.map_one`, `GroundTheory.Automorphic.Reduction.normOneGL`, `GroundTheory.Automorphic.AdelicGLn.det`, `GroundTheory.Automorphic.AdelicGLn.AdelicGL`, `GroundTheory.Automorphic.GLnLocal.integralGL`, `GroundTheory.Automorphic.HermitianForm`, `GroundTheory.Automorphic.AutomorphicForm.archGroup`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.AutomorphicForms.AdelicDixmierMalliavinProduct GroundTheory.AutomorphicForms.AdelicGLn GroundTheory.AutomorphicForms.AdelicUnitaryGroups` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 91329 LOC)

## Work Order 15: `Ground Theory / Profinite Cohomology` (`cluster-49`)

- **Internal LOC:** 53,363 (5153 declarations; bookkeeping ratio 12.8%)
- **Formal Interface Width:** 500 (leverage ratio 106.73 LOC/item)
- **Estimated Savings:** ~8,004 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.Global.FiniteSubfield`, `GroundTheory.LocalField.FormalGroup.Hom.comp`, `GroundTheory.LocalField.FormalGroup.IsLubinTateLift.comp`, `GroundTheory.Global.SemiLocal.PlacesOver`, `GroundTheory.GroupCoh.IsTateDelta.comp`, `GroundTheory.Global.IdeleGroup`, `GroundTheory.Global.FiniteSubfield.restrictHom`, `GroundTheory.GroupCoh.cupCochain`
- **Outputs (must preserve exactly):** `GroundTheory.ProfCoh.IsDiscreteRep`, `GroundTheory.ProfCoh.maxUnramifiedOutside`, `GroundTheory.ProfCoh.galUnramifiedOutside`, `GroundTheory.ProfCoh.cohomology`, `GroundTheory.ProfCoh.UnitsModPow.pow_eq_one`, `GroundTheory.ProfCoh.cocycleι`, `GroundTheory.ProfCoh.cochainOf`, `GroundTheory.ProfCoh.cocycles`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.ProfiniteCohomology.AdditiveHilbert GroundTheory.ProfiniteCohomology.Bridge GroundTheory.ProfiniteCohomology.CartierDual` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 53363 LOC)

## Work Order 16: `Formalism: theorem MV7` (`cluster-78`)

- **Internal LOC:** 38,869 (3405 declarations; bookkeeping ratio 10.8%)
- **Formal Interface Width:** 500 (leverage ratio 77.74 LOC/item)
- **Estimated Savings:** ~5,875 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.GM.M.Letters`, `Formalism.GM.M.glAct`, `Formalism.DworkPowerSeriesWeights.Integral`, `Formalism.GM.M.BlockData`, `Formalism.GM.DimensionMonotonicity.GlW`, `Formalism.GM.M.Pol`, `Formalism.GM.M.IntPol`, `Formalism.GM.M.wt`
- **Outputs (must preserve exactly):** `Formalism.InvariantFactorPaths.BranchingDimensions.Letters.k`, `Formalism.InvariantFactorPaths.G7.at1`, `Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.star`, `Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.star_star`, `Formalism.InvariantFactorPaths.G7.lgF`, `Formalism.InvariantFactorPaths.G7.UnrOK`, `Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.rev`, `Formalism.InvariantFactorPaths.BranchingDimensions.Interl.rev`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.GrowthSums.FactorialBaseGrowth.Coarse Formalism.GrowthSums.FactorialBaseGrowth.Harmonic Formalism.GrowthSums.FactorialBaseGrowth.KapPrime` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 38869 LOC)

## Work Order 17: `Formalism / GL3 Mean Squares: li Stat` (`cluster-100`)

- **Internal LOC:** 44,498 (2641 declarations; bookkeeping ratio 9.5%)
- **Formal Interface Width:** 400 (leverage ratio 111.25 LOC/item)
- **Estimated Savings:** ~6,674 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.HermitianLatticesTheory.IsCMUnram`, `Formalism.HermitianLatticesTheory.IsIntegralLat`, `Formalism.HermitianLatticesTheory.isom`, `Formalism.HermitianLatticesTheory.gmap`, `Formalism.HermitianLatticesTheory.conjIdeal`, `Formalism.ZeroFreeDirichlet.negLD`, `Formalism.HermitianLatticesTheory.fDeg`, `Formalism.HermitianLatticesTheory.hcompl`
- **Outputs (must preserve exactly):** `Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.inner`, `Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.cm`, `Formalism.HermitianLattices.GL2PrimeSums.PP`, `Formalism.HermitianLattices.Ext.L3.HU.Ent.det`, `Formalism.HermitianLattices.RamifiedLatticeOperators.Gl`, `Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.ne_bot`, `Formalism.HermitianLattices.Ext.L3.U0.Dv.star`, `Formalism.HermitianLattices.Ext.L3.IsFixF`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.GL3MeanSquares.AffineFibreCountComparison Formalism.GL3MeanSquares.ConcavityEquidistribution Formalism.GL3MeanSquares.CongruenceTorsion` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 44498 LOC)

## Work Order 18: `Companion Theory / Automorphic Theory: is Closed unit Ball` (`cluster-108`)

- **Internal LOC:** 31,401 (2348 declarations; bookkeeping ratio 9.3%)
- **Formal Interface Width:** 500 (leverage ratio 62.8 LOC/item)
- **Estimated Savings:** ~4,771 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.FourierDecayAlt.M.Par`, `Formalism.FourierDecayAlt.ThreeDimData.Mx`, `Formalism.FourierDecayAlt.B.Mat`, `BranchingSupport.Rep`, `Formalism.FourierDecayAlt.C.HidaSetting.r`, `Formalism.FourierDecayAlt.C.HidaSetting.σ`, `GlobalTheory.LocGL.IrrGL`, `Formalism.FourierDecayAlt.R.LevelData`
- **Outputs (must preserve exactly):** `CompanionTheory.Zuck.M`, `CompanionTheory.Split.exists_ne`, `CompanionTheory.LimBd.URep.UnitaryRep.map_mul`, `CompanionTheory.Zuck.URep`, `CompanionTheory.Zuck.L`, `CompanionTheory.Bmu.Hq`, `CompanionTheory.Zuck.Obj`, `CompanionTheory.LimBd.URep.UnitaryRep.map_one`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.ContinuousOnOrbit` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 31401 LOC)

## Work Order 19: `Ground Theory: discrete Topology principal Subgroup` (`cluster-47`)

- **Internal LOC:** 43,787 (4510 declarations; bookkeeping ratio 22.5%)
- **Formal Interface Width:** 500 (leverage ratio 87.57 LOC/item)
- **Estimated Savings:** ~6,568 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.Arith.Abelian.Isogeny`, `GroundTheory.LocalField.FormalGroup.Hom.comp`, `GroundTheory.Arith.Abelian.Isogeny.comp`, `GroundTheory.FunctionField.Place.ResidueField`, `GroundTheory.Arith.Abelian.genX`, `GroundTheory.Arith.Abelian.IsGenPt`, `GroundTheory.Arith.Abelian.genericPoint`, `GroundTheory.Arith.Abelian.genY`
- **Outputs (must preserve exactly):** `GroundTheory.Global.FiniteSubfield`, `GroundTheory.Global.IdeleGroup`, `GroundTheory.Global.SemiLocal.PlacesOver`, `GroundTheory.Global.IdeleGroup.ideleModule`, `GroundTheory.Global.IdeleGroup.diagonal`, `GroundTheory.Global.HeckeCharacter`, `GroundTheory.Global.SemiLocal.CompletionsOver`, `GroundTheory.Global.integralFiniteAdeles`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.GlobalFields.Adele.Approximation GroundTheory.GlobalFields.Adele.BaseChange GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 43787 LOC)

## Work Order 20: `Positivity Theory / Automorphic Forms: integral plus` (`cluster-53`)

- **Internal LOC:** 31,232 (2839 declarations; bookkeeping ratio 13.2%)
- **Formal Interface Width:** 500 (leverage ratio 62.46 LOC/item)
- **Estimated Savings:** ~4,684 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GlobalTheory.CuspRep.Ad`, `GlobalTheory.CuspRep.GA`, `UpperTheory.V.TR.Rinf`, `GlobalTheory.Serre.Lie.map_mul`, `Formalism.L2.Host.HChar`, `GlobalTheory.CuspRep.Af`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `GlobalTheory.ZH.ThetaSys.Real`
- **Outputs (must preserve exactly):** `UpperTheory.CBC.Cusp`, `GlobalTheory.RealGal.QCM`, `UpperTheory.TNZ.Grp`, `UpperTheory.TNZ.Grp.e`, `UpperTheory.CBC.Cusp.ConjIso`, `UpperTheory.CBC.Cusp.locComp`, `UpperTheory.TNZ.HasDetVec`, `UpperTheory.CBC.SatakeParameterExistence.re`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build PositivityTheory.AutomorphicForms.PublishedInputs.BorelInjectivity.EquivariantProjections.ExistsEquivariantProjOfLeSumIrreducible PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.EulDefs` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 31232 LOC)
