# Kernel-Checked Refactoring Plan

Total selected work orders: **20**

| # | Target | Scope | Internal LOC | Interface Width | Est. Savings | Priority | Rationale |
|---:|---|---|---:|---:|---:|---:|---|
| 1 | `Development / Abelian Variety Theory: cube Theorem` | cluster | 919,447 | 500 | 286,302 | 666175.7 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 2 | `Development / Automorphic Arithmetic: pt All holds` | cluster | 311,014 | 500 | 46,652 | 146853.1 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 3 | `Development / Automorphic Spectrum: cube theorem of perfect` | cluster | 253,854 | 500 | 52,254 | 144586.4 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 4 | `Development / Weil Bound: cube Theorem holds` | cluster | 173,145 | 500 | 25,971 | 81958.6 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 5 | `Ground Theory / Heights And Theta: proof` | cluster | 161,050 | 500 | 24,157 | 79797.2 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 6 | `Development / Resolution Of Singularities: exists is Blowup Along Ideal Sheaf` | cluster | 96,926 | 79 | 14,538 | 41993.7 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 7 | `Development / Etale Cohomology: graph Patch` | cluster | 40,705 | 485 | 6,105 | 21732.4 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 8 | `Reciprocity Theory / Reductive Groups: iso Cand compat` | cluster | 42,643 | 382 | 6,396 | 19023.5 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 9 | `Ground Theory / Automorphic Forms: is Finite Measure quotient Measure` | cluster | 50,054 | 342 | 7,508 | 18693.4 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 10 | `Formalism: good Emb good Of` | cluster | 16,999 | 500 | 2,549 | 8689.5 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 11 | `Ground Theory / Global Fields: omega At add` | cluster | 23,225 | 472 | 3,483 | 8582.5 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 12 | `Formalism: ps Trunc eq` | cluster | 11,496 | 500 | 1,938 | 6683.9 | high_internal_loc, duplicate_lemmas, hypothesis_slack |
| 13 | `Ground Theory / Local Fields: exists eq nsmul of proj eq zero` | cluster | 15,229 | 274 | 2,284 | 5935.4 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 14 | `Ground Theory / Arithmetic Geometry: good succ` | cluster | 12,242 | 199 | 1,836 | 4807.4 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 15 | `Ground Theory / P Adic Hodge: dvd of norm untilt le` | cluster | 11,962 | 333 | 1,794 | 4568.7 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 16 | `Formalism / Satake Dual Weyl: wlocal global` | cluster | 8,671 | 254 | 1,300 | 4324.9 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 17 | `Ground Theory / Profinite Cohomology: euler Char galois` | cluster | 11,387 | 197 | 1,708 | 4308.9 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 18 | `Reciprocity Theory / Analytic Forms: segre Ideal is Homogeneous` | cluster | 7,106 | 254 | 1,296 | 3769.8 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 19 | `Formalism / Graded Weyl Divisibility: dual Weyl Module Row Action Stable` | cluster | 4,486 | 81 | 1,220 | 3327.7 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |
| 20 | `Reciprocity Theory / L2 Dbar Estimates: hy` | cluster | 5,765 | 33 | 864 | 2870.8 | high_internal_loc, narrow_interface, duplicate_lemmas, hypothesis_slack |

## Work Order 1: `Development / Abelian Variety Theory: cube Theorem` (`cluster-34`)

- **Internal LOC:** 919,447 (70260 declarations; bookkeeping ratio 14.3%)
- **Formal Interface Width:** 500 (leverage ratio 1838.89 LOC/item)
- **Estimated Savings:** ~286,302 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp`, `ReciprocityTheory.ChartRestriction.G.Semi.LB`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme`, `Formalism.BasicNotions.ColumnChain.K`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.V`, `ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb`
- **Outputs (must preserve exactly):** `GlobalTheory.CuspRep.GA`, `GlobalTheory.BCT.Pl`, `GlobalTheory.CuspRep.Sm`, `GlobalTheory.LGrp.LeviDatum.L`, `GlobalTheory.BCT.GLw`, `GlobalTheory.LocGL.IrrGL`, `GlobalTheory.CuspRep.Af`, `GlobalTheory.CuspRep.Ad`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.LevelStructureForms Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.MultiplicationEtaleTorsion Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 919447 LOC)

## Work Order 2: `Development / Automorphic Arithmetic: pt All holds` (`cluster-106`)

- **Internal LOC:** 311,014 (22667 declarations; bookkeeping ratio 7.0%)
- **Formal Interface Width:** 500 (leverage ratio 622.03 LOC/item)
- **Estimated Savings:** ~46,652 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `Formalism.MainNotions.S.RowsAut.D`, `Formalism.BasicNotions.ColumnChain.K`, `Formalism.GradedWeylDivisibility.hw`, `Formalism.L2.DIV.RecNums.hu`, `Formalism.HC.HostRaw.F`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp`, `Formalism.BasicNotions.Scale.A`
- **Outputs (must preserve exactly):** `GlobalTheory.CuspRep.BlockIx`, `GlobalTheory.CuspRep.unip`, `Reformulated.AutPerF.Bst.u`, `UpperTheory.Reformulated.B.JumpSetsAlt.hcl`, `Reformulated.AutPerF.Acris.t`, `Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapMulVolumeOfSubgroup::key`, `Reformulated.AutPerF.Ainf`, `GlobalTheory.CuspRep.invT`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.AutomorphicArithmetic.AdelicGluing.BaseChangeLevelIsOpenIsCompactContainsIwahori Development.AutomorphicArithmetic.AdelicGluing.CommuteHeckeOperatorFiniteConvolutionOfFreeIndic Development.AutomorphicArithmetic.AdelicGluing.CuspidalProjectionCcStarTensIsLeftSmooth` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 311014 LOC)

## Work Order 3: `Development / Automorphic Spectrum: cube theorem of perfect` (`cluster-41`)

- **Internal LOC:** 253,854 (20375 declarations; bookkeeping ratio 13.8%)
- **Formal Interface Width:** 500 (leverage ratio 507.71 LOC/item)
- **Estimated Savings:** ~52,254 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `PositivityTheory.RgTw.Mat`, `PositivityTheory.RgBcC.GLs`, `GlobalTheory.BZMir.Mir`, `GlobalTheory.CuspRep.GA`, `GlobalTheory.LGrp.LeviDatum.L`, `GlobalTheory.BCT.Pl`, `GlobalTheory.PRep.IsSmooth`, `GlobalTheory.CuspRep.Sm`
- **Outputs (must preserve exactly):** `GlobalTheory.CompanionTheory.CTFin.lev`, `GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness`, `GlobalTheory.CompanionTheory.TensOne.hv`, `GlobalTheory.CompanionTheory.CTFin.CapFactor.levPair`, `GlobalTheory.CompanionTheory.BZCuspPair.irrAdm`, `GlobalTheory.CompanionTheory.Rodier.wOpen`, `GlobalTheory.CompanionTheory.Rodier.pm`, `GlobalTheory.CompanionTheory.HintLevel.hint_eq_level`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 253854 LOC)

## Work Order 4: `Development / Weil Bound: cube Theorem holds` (`cluster-40`)

- **Internal LOC:** 173,145 (16940 declarations; bookkeeping ratio 7.2%)
- **Formal Interface Width:** 500 (leverage ratio 346.29 LOC/item)
- **Estimated Savings:** ~25,971 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GlobalTheory.CuspRep.GA`, `GlobalTheory.BCT.Pl`, `GlobalTheory.CuspRep.Sm`, `Formalism.BasicNotions.LocWach.X`, `GlobalTheory.RootEx.N`, `GlobalTheory.BCT.GLw`, `GlobalTheory.CuspRep.Ad`, `Formalism.BasicNotions.ColumnChain.K`
- **Outputs (must preserve exactly):** `PositivityTheory.RgTw.Mat`, `PositivityTheory.RgBcC.GLs`, `GlobalTheory.BZMir.Mir`, `CrystallineSemistableComparison.PAlg`, `PositivityTheory.RgTw.G`, `CrystallineSemistableComparison.Cx.B`, `PositivityTheory.Rg.BcB.E.H`, `CrystallineSemistableComparison.CH.Cn`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ChooseFac Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompAdd Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.DpOfPre` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 173145 LOC)

## Work Order 5: `Ground Theory / Heights And Theta: proof` (`cluster-29`)

- **Internal LOC:** 161,050 (10893 declarations; bookkeeping ratio 8.1%)
- **Formal Interface Width:** 500 (leverage ratio 322.1 LOC/item)
- **Estimated Savings:** ~24,157 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `ReciprocityTheory.ChartRestriction.G.Geo.MRing`, `ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog`, `ReciprocityTheory.ChartRestriction.G.Geo.MRingOver`, `ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal`, `ReciprocityTheory.ChartRestriction.G.Geo.HermLine`, `ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar`, `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Ix`, `ReciprocityTheory.ChartRestriction.G.Geo.mcPts`
- **Outputs (must preserve exactly):** `GroundTheory.Heights₂.Heights.Kleiman.StepData.J`, `GroundTheory.Heights₂.Heights.chartProjMatrix`, `GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement`, `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.locIn`, `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.oneBlock`, `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.LineBundle`, `GroundTheory.Heights₂.Heights.FieldNumbers.relDim`, `GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist.F`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects GroundTheory.HeightsAndTheta.Heights.Antisymmetric.PNefOnFibresRelabel GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 161050 LOC)

## Work Order 6: `Development / Resolution Of Singularities: exists is Blowup Along Ideal Sheaf` (`cluster-14`)

- **Internal LOC:** 96,926 (5961 declarations; bookkeeping ratio 11.0%)
- **Formal Interface Width:** 79 (leverage ratio 1226.91 LOC/item)
- **Estimated Savings:** ~14,538 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Outputs (must preserve exactly):** `FunctorialResolution.Blowup.chartFraction`, `FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf`, `FunctorialResolution.Blowup.reesGrading`, `FunctorialResolution.BlowupSequence`, `FunctorialResolution.Blowup.chartRingHom`, `FunctorialResolution.Blowup.affineBlowupChart`, `FunctorialResolution.Blowup.reesGenerator`, `AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ClopenSubscheme Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.CoproductBaseChange Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DerivationLocalization` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 96926 LOC)

## Work Order 7: `Development / Etale Cohomology: graph Patch` (`cluster-35`)

- **Internal LOC:** 40,705 (4740 declarations; bookkeeping ratio 6.6%)
- **Formal Interface Width:** 485 (leverage ratio 83.93 LOC/item)
- **Estimated Savings:** ~6,105 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GlobalTheory.EtC.Shv`, `GlobalTheory.EtC.sch`, `GlobalTheory.EtC.Sec`, `GlobalTheory.EtC.tw`, `GlobalTheory.EtC.Spc`, `GlobalTheory.EtC.Sec.res`, `GlobalTheory.EtC.chains`, `GlobalTheory.EtC.Cx`
- **Outputs (must preserve exactly):** `LateralTheory.E.E4.Sp`, `LateralTheory.E.EtaleTopologySheaves.SShv`, `LateralTheory.E.E4.pl`, `LateralTheory.E.LeafDescendVCut.incl`, `LateralTheory.E.EtaleTopologySheaves.EtTop`, `LateralTheory.E.E4.IsCurve`, `LateralTheory.E.E4.pl_comp`, `LateralTheory.E.EtaleTopologySheaves.resY`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Development.EtaleCohomology.CohomologicalPurity.InrFold Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf Development.EtaleCohomology.CohomologicalPurity.LeafImgPf` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 40705 LOC)

## Work Order 8: `Reciprocity Theory / Reductive Groups: iso Cand compat` (`cluster-24`)

- **Internal LOC:** 42,643 (4162 declarations; bookkeeping ratio 8.3%)
- **Formal Interface Width:** 382 (leverage ratio 111.63 LOC/item)
- **Estimated Savings:** ~6,396 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `ReciprocityTheory.L2DbarEstimates.V`, `ReciprocityTheory.AnForm.M.FinHolAtlas`, `Formalism.QuantumDeterminants.Hpk`, `Formalism.L2.Pj.TRing.R`, `Formalism.L2.Pj.smT`, `Formalism.REAL.KRel`, `ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq`, `ReciprocityTheory.AnForm.M.IsPotential`
- **Outputs (must preserve exactly):** `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp`, `ReciprocityTheory.ChartRestriction.G.Semi.LB`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap`, `ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.V`, `ReciprocityTheory.ChartRestriction.G.Geo.MRing`, `ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback`, `ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Lemmata.FirstBlockLemmaA.Imports Lemmata.FirstBlockLemmaB.Imports Lemmata.FirstBlockLemmaK.Imports` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 42643 LOC)

## Work Order 9: `Ground Theory / Automorphic Forms: is Finite Measure quotient Measure` (`cluster-63`)

- **Internal LOC:** 50,054 (4518 declarations; bookkeeping ratio 12.9%)
- **Formal Interface Width:** 342 (leverage ratio 146.36 LOC/item)
- **Estimated Savings:** ~7,508 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.Global.IdeleGroup`, `GroundTheory.Global.IdeleGroup.ideleModule`, `GroundTheory.Global.adelicChar`, `GroundTheory.Global.fundamentalSet`, `GroundTheory.Global.IdeleGroup.diagonal`, `GroundTheory.Global.adeleMeasure`, `GroundTheory.Global.posRealUnitInterval`, `GroundTheory.Global.posRealToUnits`
- **Outputs (must preserve exactly):** `GroundTheory.Automorphic.Reduction.normOneGL`, `GroundTheory.Automorphic.AdelicGLn.AdelicGL`, `GroundTheory.Automorphic.AutomorphicForm.archGroup`, `GroundTheory.Automorphic.GLnLocal.integralGL`, `GroundTheory.Automorphic.Reduction.rationalGLOne`, `GroundTheory.Automorphic.AutomorphicForm.isExpLieAlgebra`, `GroundTheory.Automorphic.AutomorphicForm.finEmb`, `GroundTheory.Automorphic.AdelicGLn.diagonal`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.AutomorphicForms.AdelicGLn GroundTheory.AutomorphicForms.AdelicUnitaryGroups GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Restricted` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 50054 LOC)

## Work Order 10: `Formalism: good Emb good Of` (`cluster-97`)

- **Internal LOC:** 16,999 (3066 declarations; bookkeeping ratio 6.0%)
- **Formal Interface Width:** 500 (leverage ratio 34.0 LOC/item)
- **Estimated Savings:** ~2,549 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.BasicNotions.D7`, `Formalism.BasicNotions.ColumnChain.K`, `Formalism.MainNotions.S.RowsAut.D`, `Formalism.HC.HostRaw.F`, `Formalism.BasicNotions.TH.HSp`, `Formalism.BasicNotions.DivData.R`, `Formalism.BasicNotions.LocWach.X`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`
- **Outputs (must preserve exactly):** `Formalism.L2.DIV.RecNums.hu`, `Formalism.L2.Pj.DeltaDat.w`, `Formalism.L2.Indef.Tree.OnObj.C`, `Formalism.L2.Col.CoefPk.V`, `Formalism.L2.Pj.LawsCore.hle`, `Formalism.L2.Indef.Tree.OnObj.Y`, `Formalism.L2.Host.HChar`, `Formalism.L2.DIV.CSD.H`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.LocalToGlobal.AdelicCompactOpens.IntAdelesCompactOpen Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 16999 LOC)

## Work Order 11: `Ground Theory / Global Fields: omega At add` (`cluster-28`)

- **Internal LOC:** 23,225 (2584 declarations; bookkeeping ratio 22.3%)
- **Formal Interface Width:** 472 (leverage ratio 49.21 LOC/item)
- **Estimated Savings:** ~3,483 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.Arith.Abelian.Isogeny`, `GroundTheory.Arith.Abelian.isogHom`, `GroundTheory.Arith.Abelian.IsGenPt`, `GroundTheory.Arith.Abelian.genX`, `GroundTheory.Arith.Abelian.genericPoint`, `GroundTheory.LocalField.normUnits`, `GroundTheory.LocalField.Abstract.norm`, `GroundTheory.LocalField.Abstract.fixedModule`
- **Outputs (must preserve exactly):** `GroundTheory.Global.SemiLocal.PlacesOver`, `GroundTheory.Global.SemiLocal.CompletionsOver`, `GroundTheory.Global.SemiLocal.completionMap`, `GroundTheory.Global.IdeleGroup.ideleModule`, `GroundTheory.Global.IdeleGroup`, `GroundTheory.Global.AdeleBaseChange.below`, `GroundTheory.Global.AdeleBaseChange.adeleMap`, `GroundTheory.Global.ideleNorm`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.GlobalFields.Adele.Approximation GroundTheory.GlobalFields.Adele.BaseChange GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 23225 LOC)

## Work Order 12: `Formalism: ps Trunc eq` (`cluster-95`)

- **Internal LOC:** 11,496 (2024 declarations; bookkeeping ratio 3.5%)
- **Formal Interface Width:** 500 (leverage ratio 22.99 LOC/item)
- **Estimated Savings:** ~1,938 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.BasicNotions.D7`, `Formalism.BasicNotions.Ranks.N`, `Formalism.BasicNotions.ColumnChain.K`, `Formalism.BasicNotions.Scale.L`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `Formalism.BasicNotions.DivData.R`, `Formalism.ConjugateSelfDual.G`, `Formalism.BasicNotions.SizeData₂`
- **Outputs (must preserve exactly):** `Formalism.MainNotions.S.RowsAut.D`, `Formalism.HC.HostRaw.F`, `Formalism.BasicNotions.LocWach.X`, `Formalism.MainNotions.G.Level.M`, `Formalism.MainNotions.Lnk.Mod.w`, `Formalism.BasicNotions.Loc.FinExt`, `Formalism.BasicNotions.Loc.Om`, `Formalism.BasicNotions.Loc.GK`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.GaussIdealIdentity.StatementLA Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 11496 LOC)

## Work Order 13: `Ground Theory / Local Fields: exists eq nsmul of proj eq zero` (`cluster-26`)

- **Internal LOC:** 15,229 (1670 declarations; bookkeeping ratio 21.4%)
- **Formal Interface Width:** 274 (leverage ratio 55.58 LOC/item)
- **Estimated Savings:** ~2,284 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.Global.cycNorm`, `GroundTheory.Global.cycSubOne`, `GroundTheory.Global.cycHerbrand`, `GroundTheory.GroupCoh.HasHerbrandQuotient`, `GroundTheory.Global.cycNorm_cycSubOne`, `GroundTheory.Global.cycSubOne_cycNorm`, `GroundTheory.Global.cycSubOne_apply`, `GroundTheory.Global.filtrationComplete_unitFiltration`
- **Outputs (must preserve exactly):** `GroundTheory.LocalField.Abstract.ClassFieldData.valuation`, `GroundTheory.LocalField.lowerRamificationGroup`, `GroundTheory.LocalField.IsIrrCharacter.one_ne_zero`, `GroundTheory.LocalField.normUnits`, `GroundTheory.LocalField.maximalAbelianExtension`, `GroundTheory.LocalField.ord`, `GroundTheory.LocalField.ramificationIndex`, `GroundTheory.LocalField.upperRamificationGroup`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule GroundTheory.LocalFields.AbstractLocalReciprocity.Frobenius` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 15229 LOC)

## Work Order 14: `Ground Theory / Arithmetic Geometry: good succ` (`cluster-19`)

- **Internal LOC:** 12,242 (1351 declarations; bookkeeping ratio 12.1%)
- **Formal Interface Width:** 199 (leverage ratio 61.52 LOC/item)
- **Estimated Savings:** ~1,836 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.FunctionField.IsFunctionField`, `GroundTheory.FunctionField.Divisor.A`, `GroundTheory.FunctionField.essFiniteType`, `GroundTheory.FunctionField.trdeg_eq_one`
- **Outputs (must preserve exactly):** `GroundTheory.Arith.SchemeCoh.d`, `GroundTheory.Arith.Abelian.Isogeny`, `GroundTheory.Arith.SchemeCoh.ProjSpace.grading`, `GroundTheory.Arith.Abelian.isogHom`, `GroundTheory.Arith.Abelian.IsGenPt`, `GroundTheory.Arith.Abelian.genX`, `GroundTheory.Arith.SchemeCoh.modulesAb`, `GroundTheory.Arith.SchemeCoh.inter`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisionPoints GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 12242 LOC)

## Work Order 15: `Ground Theory / P Adic Hodge: dvd of norm untilt le` (`cluster-38`)

- **Internal LOC:** 11,962 (1341 declarations; bookkeeping ratio 18.3%)
- **Formal Interface Width:** 333 (leverage ratio 35.92 LOC/item)
- **Estimated Savings:** ~1,794 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.LocalField.upperRamificationGroup`, `GroundTheory.LocalField.algebraicNormedField`, `GroundTheory.LocalField.lowerRamificationGroup`, `GroundTheory.LocalField.unramifiedDegree`, `GroundTheory.LocalField.unitFiltrationUnits`, `GroundTheory.LocalField.absRamificationIndex`, `GroundTheory.LocalField.maximalAbelianExtension`, `GroundTheory.LocalField.ord`
- **Outputs (must preserve exactly):** `GroundTheory.PAdicHodge.APFData.F`, `GroundTheory.PAdicHodge.NormTower.N`, `GroundTheory.PAdicHodge.normInteger`, `GroundTheory.PAdicHodge.pFlat`, `GroundTheory.PAdicHodge.TeichLift.B`, `GroundTheory.PAdicHodge.untilt_epsilon`, `GroundTheory.PAdicHodge.ACris.galCris`, `GroundTheory.PAdicHodge.ACris.ACris`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.PAdicHodge.ACrisBdR GroundTheory.PAdicHodge.ACrisBdRGalois GroundTheory.PAdicHodge.ACrisBdRInj` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 11962 LOC)

## Work Order 16: `Formalism / Satake Dual Weyl: wlocal global` (`cluster-88`)

- **Internal LOC:** 8,671 (728 declarations; bookkeeping ratio 12.2%)
- **Formal Interface Width:** 254 (leverage ratio 34.14 LOC/item)
- **Estimated Savings:** ~1,300 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.HermitianLatticesTheory.gmap`, `Formalism.GradedWeylDivisibility.weyl`, `Formalism.GradedWeylDivisibility.rowAct`, `Formalism.HermitianLatticesTheory.isom`, `Formalism.HermitianLatticesTheory.dual`, `Formalism.HermitianLatticesTheory.zmap`, `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `Formalism.E.hdual`
- **Outputs (must preserve exactly):** `Formalism.UG.cT`, `Formalism.UG.ordL`, `Formalism.UG.Ov`, `Formalism.UG.GU`, `Formalism.UG.IsUnramInv`, `Formalism.UG.IsUnifV`, `Formalism.UG.Tj`, `Formalism.UG.GLint`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 8671 LOC)

## Work Order 17: `Ground Theory / Profinite Cohomology: euler Char galois` (`cluster-27`)

- **Internal LOC:** 11,387 (1182 declarations; bookkeeping ratio 16.1%)
- **Formal Interface Width:** 197 (leverage ratio 57.8 LOC/item)
- **Estimated Savings:** ~1,708 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `GroundTheory.LocalField.unitFiltration`, `GroundTheory.LocalField.IsUnramified`, `GroundTheory.LocalField.lowerRamificationGroup`, `GroundTheory.LocalField.Abstract.ClassFieldData.valuation`, `GroundTheory.LocalField.mem_unitFiltration`, `GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension`, `GroundTheory.LocalField.algebraicTopology_isValuativeTopology`, `GroundTheory.LocalField.algebraicValuativeRel`
- **Outputs (must preserve exactly):** `GroundTheory.ProfCoh.cohomology`, `GroundTheory.ProfCoh.cochainOf`, `GroundTheory.ProfCoh.cocycles`, `GroundTheory.ProfCoh.IsDiscreteRep`, `GroundTheory.ProfCoh.AdditiveFunction.g`, `GroundTheory.ProfCoh.unitsPow`, `GroundTheory.ProfCoh.cochainsComplex`, `GroundTheory.ProfCoh.cdp`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build GroundTheory.ProfiniteCohomology.AdditiveHilbert GroundTheory.ProfiniteCohomology.Bridge GroundTheory.ProfiniteCohomology.CartierDual` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 11387 LOC)

## Work Order 18: `Reciprocity Theory / Analytic Forms: segre Ideal is Homogeneous` (`cluster-23`)

- **Internal LOC:** 7,106 (607 declarations; bookkeeping ratio 14.7%)
- **Formal Interface Width:** 254 (leverage ratio 27.98 LOC/item)
- **Estimated Savings:** ~1,296 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `ReciprocityTheory.CA.exists_dim_trdeg_field`, `ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field`, `ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field`, `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain`
- **Outputs (must preserve exactly):** `ReciprocityTheory.AnForm.R.WData.M`, `ReciprocityTheory.AnForm.maDens`, `ReciprocityTheory.AnForm.M.FinHolAtlas`, `ReciprocityTheory.AnForm.hessC`, `ReciprocityTheory.AnForm.M.chartIdx`, `ReciprocityTheory.AnForm.R.IsMultiHomogIdeal`, `ReciprocityTheory.AnForm.A.jacC`, `ReciprocityTheory.AnForm.levi`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Lemmata.GeneralBFactLeftMore.Imports ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 7106 LOC)

## Work Order 19: `Formalism / Graded Weyl Divisibility: dual Weyl Module Row Action Stable` (`cluster-72`)

- **Internal LOC:** 4,486 (429 declarations; bookkeeping ratio 5.4%)
- **Formal Interface Width:** 81 (leverage ratio 55.38 LOC/item)
- **Estimated Savings:** ~1,220 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `Formalism.REAL.fockF`, `Formalism.REAL.fischerInner_add_left`, `Formalism.REAL.fischerInner_sum_left`, `Formalism.REAL.fischerInner_sum_right`, `Formalism.REAL.fischerInner_monomial_left`, `Formalism.REAL.fischerInner_eq_sum_of_subset`, `Formalism.REAL.fischerInner_X_mul_left`
- **Outputs (must preserve exactly):** `Formalism.GradedWeylDivisibility.CoeffHom.algebraMap`, `Formalism.GradedWeylDivisibility.hw`, `Formalism.GradedWeylDivisibility.rowAct`, `Formalism.GradedWeylDivisibility.dualWeyl`, `Formalism.GradedWeylDivisibility.rowGen`, `Formalism.GradedWeylDivisibility.rowDiv`, `Formalism.GradedWeylDivisibility.weyl`, `Formalism.GradedWeylDivisibility.blockAct`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Formalism.GradedWeylDivisibility.DualWeylDominanceOf Formalism.GradedWeylDivisibility.FinalB Formalism.GradedWeylDivisibility.FinalC` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 4486 LOC)

## Work Order 20: `Reciprocity Theory / L2 Dbar Estimates: hy` (`cluster-22`)

- **Internal LOC:** 5,765 (413 declarations; bookkeeping ratio 14.5%)
- **Formal Interface Width:** 33 (leverage ratio 174.7 LOC/item)
- **Estimated Savings:** ~864 LOC
- **Strategy:** Deduplicate 10 canonical signature group(s) into shared reusable lemmas. Audit 8 high-hypothesis lemma(s) for unused/redundant hypotheses and factor shared context into a tighter abstraction.
- **Inputs:** `UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim`
- **Outputs (must preserve exactly):** `ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.Flat`, `ReciprocityTheory.L2DbarEstimates.V`, `ReciprocityTheory.L2DbarEstimates.I.ev`, `ReciprocityTheory.L2DbarEstimates.Y.hy`, `ReciprocityTheory.L2DbarEstimates.F.w1`, `ReciprocityTheory.L2DbarEstimates.F.w2`, `ReciprocityTheory.L2DbarEstimates.Smooth`, `ReciprocityTheory.L2DbarEstimates.F.n2`
- **Duplicate Signature Groups:** 10
- **Verification Gate:**
  - [ ] Run `lake build Lemmata.MiscLemmasF.Imports ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq` with exit code 0
  - [ ] Confirm `#print axioms` introduces zero `sorryAx` or non-standard axioms on all exported outputs
  - [ ] Verify strict effective LOC reduction (< 5765 LOC)
