# RH_14 · 真空命题及其全部消费点（第 2 条）

根：`F:\F\BSD_GRH_RH\RH_14\lean\src`

## 一、定义为恒真的命题（`: Prop := True`）

- `trivialClassCondition` — `Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean:14`
- `SettingHypotheses` — `Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnramifiedNoJump.lean:132`
- `CanE` — `Development/AbelianVarietyTheory/Definitions/LatticeFrames/IsScaleWithBoundedGamma.lean:28`
- `TrivialRankCondition` — `Development/AbelianVarietyTheory/Definitions/LatticeFrames/NotInhAbsOfGamLe.lean:36`
- `UnusedSlot55` — `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean:89`
- `NoCondition` — `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean:90`
- `UpperTheory.One.M.TrivialCondition` — `Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/SwOn.lean:5`
- `GlobalTheory.Published.UnusedSlot72` — `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`
- `trivialClassCondition` — `Formalism/LocalToGlobal/ProjectiveLattices/RegPFree.lean:16`
- `trivialClassCondition` — `Formalism/LocalToGlobal/ProjectiveLattices/ValSetAlgSubset.lean:14`
- `SetHyp` — `Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean:327`

## 二、逐命题的消费点

### `CanE`（24 处）

分类：REF(引用) 21，SIGNATURE(槽) 2，DEF(=True) 1

- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/CanExtOfCharts.lean:17 — `namespace GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/CanExtOfCharts.lean:40 — `def CanExtOfCharts : Prop :=`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/CanExtOfCharts.lean:43 — `∃ L : ∀ ch : Chart Y.t (interior Y), Submodule Γ(Y.X, ch.U.1) (HdR ch.A), IsCanExt Y.s L`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/CanExtOfCharts.lean:45 — `end GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/FormalCanLat.lean:2 — `import Development.AbelianVarietyTheory.Definitions.Divisors.CanExtOfCharts`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/FormalCanLat.lean:9 — `open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/FormalCanLat.lean:14 — `namespace GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/FormalCanLat.lean:25 — `end GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/IntLatGEqCanLatOfSurjective.lean:9 — `open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/IntLatGEqCanLatOfSurjective.lean:14 — `namespace GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/IntLatGEqCanLatOfSurjective.lean:91 — `end GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/IntLatGEqCanLatOfSurjective.lean:95 — `open GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/LevelOfOfSameBut.lean:290 — `def CanEx : Prop := AtTw fun Fm x hx i p w j => ∃ rd : Can p w j, IsCan p rd ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/Divisors/LevelOfOfSameBut.lean:371 — `def Steps : Prop := CanEx ∧ CanProj ∧ TwAdm ∧ RowAt ∧ TieRat ∧ RecSide ∧ AdaptEx ∧ ConjBase ∧ ConjTw ∧ BaseLe ∧ BaseGe ∧ TwLe ∧ TwGe`
- `[DEF(=True)]` Development/AbelianVarietyTheory/Definitions/LatticeFrames/IsScaleWithBoundedGamma.lean:28 — `def CanE (D : D7) (_L _C' : ℝ) : Prop := TrueF D ∧ BigGap D`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/LatticeFrames/IsScaleWithBoundedGamma.lean:32 — `def StdE (D : D7) (L C' : ℝ) : Prop := CanE D L C' ∧ IsScaleWithBoundedGamma D L C'`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/CanonicalExistence.lean:225 — `theorem canEx_holds : CanEx :=`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/CanonicalExistenceStatement.lean:9 — `theorem _root_.GlobalTheory.T.canonical_existence : CanEx := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsLieBasisOfIsLocalRing.lean:9 — `open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsPolFormIsNabla.lean:10 — `open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM`
- `[REF(引用)]` Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ToroidalCompactification.lean:214 — `def IsCanExt {K : Type} [CommRing K] (s : X ⟶ Sp K)`
- `[REF(引用)]` Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ToroidalCompactification.lean:247 — `∃ L : ∀ ch : Chart Y.t (interior Y), Submodule Γ(Y.X, ch.U.1) (HdR ch.A), IsCanExt Y.s L`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CanExHoldsStatement.lean:4 — `import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHolds`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExportStOfPrints.lean:9 — `import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHoldsStatement`

### `NoCondition`（5 处）

分类：SIGNATURE(槽) 3，DEF(=True) 1，FIELD(结构字段) 1

- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/HubXTypePrimeConditions.lean:11 — `theorem noLgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → NoCondition D := fun _ _ _ _ _ => trivial`
- `[DEF(=True)]` Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean:90 — `def NoCondition (_ : D7) : Prop := True`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HubXTypePrimeConditions.lean:11 — `theorem noLgc_alt : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → NoCondition D := fun _ _ _ _ _ => trivial`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HubXTypePrimeConditions.lean:12 — `theorem hubX_typePrime_conditions_alt : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → AdmissibleParameterJ.JumpConditions L → EmbeddingTy`
- `[FIELD(结构字段)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ImportsMoreExtra.lean:37 — `have hLgc : _root_.UpperTheory.GalS.NoCondition D := _root_.UpperTheory.GalS.noLgc_alt D htie had1 had2 had5`

### `SetHyp`（88 处）

分类：REF(引用) 86，SIGNATURE(槽) 2

- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/PlaceBelowAllPowers.lean:49 — `Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/PlaceBelowAllPowers.lean:58 — `Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/ReadingAllLemmas.lean:24 — `BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/ReadingAllLemmas.lean:66 — `BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/ToricLatticeDenominators.lean:158 — `SetHyp bkP i →`
- `[REF(引用)]` Development/AbelianVarietyTheory/Counterexamples/NonGaloisSurvey/MemTypeSubspaceIffUnipotentCharacter.lean:122 — `∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AmbientBaseHeq.lean:40 — `BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (nch.twI w) ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (nch.twI w)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AmbientBaseHeq.lean:96 — `(D.ntw.NonzeroIndexPlace i ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) i) →`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AmbientBaseHeq.lean:100 — `by_cases hi : D.ntw.NonzeroIndexPlace i ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) i`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyAllIff.lean:71 — `(Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0 ∧ D.ntw.NonzeroIndexPlace (C.twI w) ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w) ∧ I.Ok (C.twI w)) →`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ParMem.lean:37 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AdmissibleIndexBoundAllPowers.lean:15 — `∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AdmissibleIndexBoundAllPowers.lean:24 — `Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnivChar.lean:160 — `hyp : ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FoundationProofs/GoodPartMemBasisSeries.lean:653 — `SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FoundationProofs/GoodPartMemBasisSeries.lean:699 — `ToricLatticeDenominators.exportAt bkP N0 i ↔ (SetHyp bkP i → RankAt bkP.ex E i) ∧ exportAll bkP bkP.ex E N0 i := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FoundationProofs/GoodPartMemBasisSeries.lean:749 — `(∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (Formalism.MainNotions.BlochKatoReduction.pin bkP) i → RankAt D.nexp E i) ∧ ExportAllConjugates D bkP E N0) ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FoundationProofs/GoodPartMemBasisSeries.lean:752 — `(∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (Formalism.MainNotions.BlochKatoReduction.pin bkP) i → RankAt D.nexp E i) ∧ ExportAllConjugates D bkP E N0 := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeafTW1OfAllConjugatesGood.lean:422 — `∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i ∧ I.Ok i`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmT4OfRationalRows.lean:5 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmT4OfRationalRowsStatement.lean:6 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSetupPinnedCh.lean:8 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTiedChoiceOfReads.lean:13 — `def TwistedPairSettingHyps (D : D7) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsToricCharactersInTwistCoefficientRings.lean:5 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsToricCharactersInTwistCoefficientRingsStatement.lean:6 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsZmodEq.lean:6 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FirstTwistCharacterEqLadicHeckeCharacter.lean:4 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FirstTwistCharactersEqLadicCharactersAllReadings.lean:4 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FirstTwistCharactersEqLadicCharactersAllReadingsStatement.lean:6 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisInputs.lean:5 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisInputs.lean:21 — `theorem galois_inputs : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (G : GalSide D), GlobalTheory.TripleLocal.GalHod`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GoodSetupCountEqZeroOffBadPlaces.lean:7 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeOperatorPreservesSupLatticeRealSide.lean:5 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeOperatorPreservesSupLatticeRealSideStatement.lean:6 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeTransformCuspFormsReadsCosetSum.lean:8 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InertiaEigenvalueTheoremOfHyp.lean:6 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RealizationOfPublished.lean:5 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RealizationOfPublishedStatement.lean:6 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeriesRealizationOfPublished.lean:5 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeriesRealizationOfPublishedStatement.lean:6 — `import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge`
- …（余 48 处，见脚本可重跑）

### `SettingHypotheses`（15 处）

分类：REF(引用) 15

- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnramifiedNoJump.lean:132 — `def SettingHypotheses (i : D.ntw.Tw) : Prop :=`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnramifiedNoJump.lean:138 — `def Row : Prop := ∀ i : D.ntw.Tw, D.ntw.NonzeroIndexPlace i → SettingHypotheses D i`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisInputs.lean:31 — `GlobalTheory.SettingHypotheses.setHyp_of_isTriple_of_galHodge hC D G.wd G.cf G.chr hGH h2 G.triple G.lam G.lamOk G.lamTie G.rank G.primes⟩`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SetHypOfIsTripleOfGalHodge.lean:12 — `namespace GlobalTheory.SettingHypotheses`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SetHypOfIsTripleOfGalHodge.lean:37 — `end GlobalTheory.SettingHypotheses`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GaloisInputs.lean:29 — `_root_.GlobalTheory.SettingHypotheses.setHyp_of_isTriple_of_nonzeroIndexPlace hC D G.wd G.cf G.chr hGH h2 G.triple G.lam G.lamOk G.lamTie G.rank G.primes⟩`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SetHypOfIsTripleOfGalHodge.lean:11 — `namespace GlobalTheory.SettingHypotheses`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SetHypOfIsTripleOfGalHodge.lean:25 — `end GlobalTheory.SettingHypotheses`
- `[REF(引用)]` Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean:1692 — `WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D ∧`
- `[REF(引用)]` Formalism/SizeWindowBrackets/Chain2aCoreNoAnalytic.lean:471 — `PrimeWindowSizeBounds.WindowSettingHypotheses P π (inertPs D N) s sB (Finset.univ : Finset (Fin m)) TT BAD Sig`
- `[REF(引用)]` Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean:341 — `def WindowSettingHypotheses (P : Par) {U Ω : Type} [Fintype Ω] (π : Ω → ℝ) (Ps s sB : Finset ℕ) (J : Finset κ)`
- `[REF(引用)]` Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean:365 — `WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D →`
- `[REF(引用)]` Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean:373 — `WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D →`
- `[REF(引用)]` Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean:397 — `WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D →`
- `[REF(引用)]` Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean:411 — `WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D ∧ J.card = 1 ∧ TT.card = 1 ∧ Ps.Nonempty ∧`

### `TrivialCondition`（16 处）

分类：SIGNATURE(槽) 8，REF(引用) 7，DEF(=True) 1

- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/ExistsCgTrueCharSide.lean:61 — `theorem cgGood (_ : TrivialCondition) (C : CGTrueT hL D T) : ∀ a (π : D.naut.CG a), GoodAll (C.e a π) := C.good`
- `[REF(引用)]` Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/ExistsCgTrueCharSide.lean:65 — `def cgMk (_ : TrivialCondition) (e : ∀ a, D.naut.CG a ↪ HostCGu D.host a) (good : ∀ a (π : D.naut.CG a), GoodAll (e a π))`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/GoodAUIso.lean:47 — `theorem sphGood (_ : TrivialCondition) {π : NG.AutRep L n} {v} (h : SphAtG π v) : NoSplit L v → GoodAU π := h.2`
- `[REF(引用)]` Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/MvAll.lean:15 — `def New.nMv (_ : TrivialCondition) {D : D7} (m : Mv D) (n : NTiedGPlaceholder D) : NTiedGPlaceholder m.D :=`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/Narrow.lean:18 — `theorem New.typeS (_s : TrivialCondition) (H : IsRecT h rc) : TypeLaw h rc := H.choose_spec.choose_spec.type`
- `[DEF(=True)]` Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/SwOn.lean:5 — `def UpperTheory.One.M.TrivialCondition : Prop := True`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/AHodgeDgalHodgeOfCgTrueG.lean:30 — `theorem galHodge0_of_cgTrue (sw : _root_.UpperTheory.One.M.TrivialCondition) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ConjTwOfOne.lean:36 — `def TwistTrivialCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => OneAt p w j`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ConjTwOfOne.lean:53 — `theorem conjTw_of_twAdm_latSmallGen_normAt_twOne (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hG : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators) (hN : _root_.GlobalTheory.BigOn.Exp.TwConj.NormCondition) (hO : _root_.GlobalTheory.BigOn.Exp.TwConj.T`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MMvDmvAll.lean:16 — `def mvAll_alt (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (m : Mv D) {C : NChoice D} (a : _root_.GlobalTheory.HeightCounting.NAllCAlt D C) : _root_.GlobalTheory.HeightCounting.NAllCAlt m.D (m.ch C) := @_root_.GlobalTheory.HeightCounting.NAllCAlt.m`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MMvDmvCg.lean:19 — `def mvCg_alt (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE}`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MMvDstA.lean:19 — `def stageAOfSwitch (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (N : TwNew D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseD`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MNarrow.lean:16 — `theorem narrowBig_alt (s : _root_.UpperTheory.One.M.TrivialCondition) (_art : GlobalTheory.Published.GlobalArtinReciprocity) (_hL : _root_.UpperTheory.Zero.LLC.RecTExists) :`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SepConjG.lean:22 — `theorem sep_conj_g_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TwOneOfSteps.lean:41 — `Φ = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧ ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val = Φ') : _root_.GlobalTheory.BigOn.Exp.TwConj.TwistTrivialCondition := by`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/UnitaryReadTrue.lean:20 — `theorem unitaryRead_true_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D),`

### `TrivialRankCondition`（3 处）

分类：SIGNATURE(槽) 2，DEF(=True) 1

- `[DEF(=True)]` Development/AbelianVarietyTheory/Definitions/LatticeFrames/NotInhAbsOfGamLe.lean:36 — `def TrivialRankCondition (_D : D7) (_L _C' : ℝ) : Prop := True`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Definitions/LatticeFrames/NotInhAbsOfGamLe.lean:94 — `theorem Row.of_noE {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Row TrivialRankCondition Q) : Row E Q := fun Cg cb Cu cT CT h1 h2 =>`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Definitions/LatticeFrames/NotInhAbsOfGamLe.lean:269 — `theorem RowsInh.gap (h : RowsInh) : InhG GapE ∧ InhG TrivialRankCondition ∧ InhG LedE :=`

### `UnusedSlot33`（199 处）

分类：REF(引用) 118，FIELD(结构字段) 54，SIGNATURE(槽) 25，DEF 2

- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DataNonvanishingAllMembers.lean:40 — `discriminant_eq_base_sq D (Formalism.MainNotions.UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D),`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormScaleCurveIdeal.lean:49 — `rw [← Formalism.MainNotions.UnusedSlot33.normK_holds D cc hc, Ideal.pointwise_smul_def]`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormScaleCurveIdeal.lean:106 — `have hs : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := Formalism.MainNotions.UnusedSlot33.PolarisationData.conj_b D`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/IndexStandardInfSkewThetaLatticeEqAbsNormPow.lean:142 — `have hN : Ideal.absNorm (D.host.conj • 𝔪) = Ideal.absNorm 𝔪 := UnusedSlot33.HK.absNorm_smul D.host 𝔪`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuadraticSubfieldRootDiscriminant.lean:54 — `have hdiff := Formalism.MainNotions.UnusedSlot33.HK.different_quad (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/TwoLeRootDiscriminantAndSplitArithmeticCondition.lean:7 — `⟨S.root_discriminant_ge_two _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _),`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/TwoLeRootDiscriminantAndSplitArithmeticCondition.lean:10 — `Formalism.L2.SG.ResidEvFree.splitsE_g _ 0, Formalism.L2.SG.ResidEvFree.splitsE_g _ 1, S.discriminant_eq_base_sq _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _)⟩`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FoundationProofs/InducedTypeThetaGenusOnePermutes.lean:14 — `open Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/FoundationProofs/PhAtMulByNorm.lean:109 — `have h := Formalism.MainNotions.UnusedSlot33.HK.norm_int D.host a`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/UniformizationHolds.lean:81 — `haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/UniformizationHolds.lean:88 — `haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntMulMemInvHalfDifferent.lean:100 — `(UnusedSlot33.HK.conj_conj H) (HostK.trace_conj H) (HostK.trace_pos H)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralHalf.lean:11 — `open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.UnusedSlot33.HK`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NoRamifiedNorm.lean:16 — `have h1 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x, hx⟩`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NoRamifiedNorm.lean:17 — `have h2 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x + 1, add_mem hx (one_mem _)⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NoRamifiedNorm.lean:109 — `have hb0 : b ≠ 0 := Formalism.MainNotions.UnusedSlot33.HK.b_ne_zero H`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NoRamifiedNorm.lean:112 — `obtain ⟨s, hs⟩ := trace_rat H ((π : H.E) / b) (div_mem hK (Formalism.MainNotions.UnusedSlot33.HK.bE_mem H))`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NoRamifiedNorm.lean:150 — `rw [tauLL, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host _ (D.eTau τ).2 _ (H.atT u).piU_K]`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ProdAbsNormDivsDvd.lean:145 — `rw [B.fields_emb_apply, B.fields_emb_apply, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K B.host _ τ.2 x hx,`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ProdAbsNormDivsDvd.lean:146 — `Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K B.host _ τ'.2 x hx]`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsStandardBasesLatticeAtPlaceOfAdaptedBases.lean:18 — `rw [UnusedSlot33.HK.cc_mul_cc, InducedType.sigmaOf_one] at this`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormProdCmEmbeddingsEqOneOfInert.lean:433 — `have hb := Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host g hgPsi _ hbK`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/ArithP.lean:39 — `open Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean:119 — `(s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i)) (s24 : StandardLattice.KudlaFamilyStatement Fm C3) :`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean:129 — `obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean:130 — `have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean:157 — `(s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean:165 — `obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean:166 — `have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x hx i => by`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean:172 — `have h22 : TaylorLogMetric.ConclusionOnFamily Fm C22 := s22 (TaylorLogMetric.AdmF_of Fm (fun x i => UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _))`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean:211 — `(s59 : ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i))`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean:832 — `rw [hh, addOrderOf_ofMul_eq_orderOf, UnusedSlot33.SlopeTestRemainingChoices.orderOf_iotaH]`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean:833 — `have := UnusedSlot33.PrimeReciprocalSums.hOf_ord D.R.e p hl2`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/GL1/Statement.lean:15 — `letI := Formalism.MainNotions.UnusedSlot33.tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GL1/Statement.lean:24 — `∀ D : Formalism.BasicNotions.D7, CompactFixesLattice → Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice D`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GL1/Statement.lean:28 — `∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice (Fm.D x i)`
- `[REF(引用)]` Formalism/LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean:251 — `obtain ⟨C₅, h59⟩ := UnusedSlot33.field_lemmas_except_seven`
- `[REF(引用)]` Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FactPrincipalDatum.lean:12 — `obtain ⟨β, hβ, heq⟩ := Formalism.MainNotions.UnusedSlot33.HK.diffK_holds H`
- `[REF(引用)]` Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FactPrincipalDatum.lean:19 — `have h := Formalism.MainNotions.UnusedSlot33.HK.normK_holds H H.ccK H.ccK_ne_bot`
- `[REF(引用)]` Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/GlobalDualOfBasis.lean:62 — `rw [Formalism.BasicNotions.Examples₂.star_eq_conj, Formalism.MainNotions.UnusedSlot33.HK.conj_conj]`
- …（余 159 处，见脚本可重跑）

### `UnusedSlot34`（67 处）

分类：REF(引用) 32，SIGNATURE(槽) 17，ARROW(前件链) 10，FIELD(结构字段) 6，DEF 2

- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableOrbitalIntegralPreservedLatticeIsometry.lean:46 — `have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsAdelicTorusMeasureStabiliserHaar.lean:11 — `theorem omT_stab_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsAdelicTorusMeasureStabiliserHaarStatement.lean:9 — `theorem _root_.GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNo`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsFrameStabilizerHaarNormalisedFibreMeasure.lean:17 — `theorem exists_tied_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsFrameStabilizerHaarNormalisedFibreMeasureStatement.lean:9 — `theorem _root_.GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formal`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalSelfDualMeasuresFibreFamilyExist.lean:14 — `∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerF`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalSelfDualMeasuresFibreFamilyExistStatement.lean:9 — `theorem _root_.GlobalTheory.T.localSelfDualMeasures_fibreFamily_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNot`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/FlagMeasures/SiegelWeilVolumes.lean:11 — `theorem siegelWeil_volumes : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND `
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierUniquenessRealComponentsAdelicHom.lean:28 — `(tauE D) θ (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (GlobalTheory.CMTypePlaces.mk_tauE_bijective D) hθ`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/MixedModelHeisenbergPhaseEqCexpRealPoints.lean:107 — `have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryQuotientHeightLeOfNoShortVector.lean:147 — `have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D`
- `[REF(引用)]` Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanMultiplierTemperate.lean:80 — `rw [GlobalTheory.PhaseReal.infPart_cA, GlobalTheory.Mem.VolExists.infEmb_sigR (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (hθ τ)]`
- `[REF(引用)]` Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousRs.lean:46 — `· have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D`
- `[REF(引用)]` Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InjectivePairingFiniteFamily.lean:105 — `have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D`
- `[REF(引用)]` Development/AutomorphicSpectrum/Proofs/GlobalProofs/RationalUnipotentLeParabolic.lean:22 — `have hCM := Formalism.MainNotions.UnusedSlot34.isCMExt_D D`
- `[FIELD(结构字段)]` Development/WeilBound/RepresentationTheoryGL/SiegelWeil/ArchimedeanSiegelWeil/PlaceIntegrals/SiegelWeilRankCoefficient.lean:20 — `have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := Formalism.MainNotions.UnusedSlot34.isCMExt_D D`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/GL5/Statement.lean:40 — `Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWa1 ∧ Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWa2 ∧`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/GL5/Statement.lean:41 — `Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWb1 ∧ Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWb2 ∧`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/GL5/Statement.lean:42 — `Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWc1 ∧ Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWc2 ∧`
- `[REF(引用)]` Formalism/LocalToGlobal/GlobalTheory/GL5/Statement.lean:43 — `Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWc3`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/GlobalTheory/GL5/Statement.lean:99 — `∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), WeilSiegelGauge → Formalism.MainNotions.UnusedSlot34.KudlaFamilyStatement Fm`
- `[REF(引用)]` Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedVolumeStatements/VolumeNormalizedOne.lean:26 — `unfold Formalism.MainNotions.UnusedSlot34.ForAllCM at *`
- `[REF(引用)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/Volumes.lean:118 — `Formalism.MainNotions.UnusedSlot34.ForAllCM fun F E _ _ _ _ σ M J =>`
- `[ARROW(前件链)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/Volumes.lean:119 — `Formalism.MainNotions.UnusedSlot34.SWa1 F E σ M J → Formalism.MainNotions.UnusedSlot34.SWc1 F E σ M J →`
- `[DEF]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/Volumes.lean:122 — `def VolumeUnipotentAllCM : Prop := Formalism.MainNotions.UnusedSlot34.ForAllCM fun F E _ _ _ _ σ M J => VolumeUnipotent F E σ M J`
- `[DEF]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/Volumes.lean:124 — `def LevelSAll : Prop := Formalism.MainNotions.UnusedSlot34.ForAllCM fun F E _ _ _ _ σ M J => LevelS F E σ M J`
- `[REF(引用)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/Volumes.lean:151 — `Formalism.MainNotions.UnusedSlot34.ForAllCM fun F E _ _ _ _ σ M J =>`
- `[ARROW(前件链)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/Volumes.lean:152 — `Formalism.MainNotions.UnusedSlot34.SWa1 F E σ M J → VolStab F E σ M J → VolumeIsotropicTuple F E σ M J → VolumeUnipotent F E σ M J →`
- `[REF(引用)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MassDataChoiceLeaves.lean:29 — `Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ∧`
- `[REF(引用)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MassDataChoiceLeaves.lean:59 — `Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ∧`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcAllS.lean:41 — `(hSW1 : Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)`
- `[ARROW(前件链)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcSFinVolSk.lean:42 — `StdHyp σ J ψ → (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcSplit.lean:21 — `StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → (gramE σ J (tupH P)).det ≠ 0 → 2 * (r + 1 + r) < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →`
- `[FIELD(结构字段)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcSplitS.lean:19 — `StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → (gramE σ J (tupH P)).det ≠ 0 → 2 * (r + 1 + r) < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →`
- `[ARROW(前件链)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcSSplitSk.lean:42 — `StdHyp σ J ψ → (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →`
- `[ARROW(前件链)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcSSplitSk.lean:60 — `StdHyp σ J ψ → (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →`
- `[REF(引用)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcWeil.lean:8 — `open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnusedSlot34 Formalism.L2.SG.Volumes NumberField IsDedekindDomain MeasureTheory`
- `[REF(引用)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcWeil.lean:54 — `Formalism.MainNotions.UnusedSlot34.ForAllCM fun F E _ _ _ _ σ M J =>`
- `[ARROW(前件链)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcWeil.lean:55 — `Formalism.MainNotions.UnusedSlot34.SWa1 F E σ M J → SWc1W F E σ M J → VolStabW F E σ M J ∧ VolumeLargeRank F E σ M J`
- `[ARROW(前件链)]` Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcXFinVolSk.lean:42 — `StdHyp σ J ψ → (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →`
- …（余 27 处，见脚本可重跑）

### `UnusedSlot35`（24 处）

分类：REF(引用) 19，ARROW(前件链) 3，FIELD(结构字段) 2

- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GammaOperatorSemisimpleOfConclusions.lean:76 — `rw [Formalism.MainNotions.UnusedSlot35.DssRec.coreDss_iff_mem _ h9]`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GammaSubOneDivUniformiserAtLetterOfConclusions.lean:49 — `refine ⟨Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj (E := W.EE) _ hqYu ?_, ?_⟩`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GammaSubOneDivUniformiserAtLetterOfConclusions.lean:86 — `rw [Formalism.MainNotions.UnusedSlot35.DssRec.dssLet_iff_mem _ h9]`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GammaSubOneDivUniformiserAtLetterOfConclusions.lean:116 — `have hqu := qp_isUnit _ (Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit _ h9 hA T hT)`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LiftingTheoremWachModuleLemmaHypothesesAdmitted.lean:26 — `have h17 : LiftingTheory.adm17 D HW F := Formalism.MainNotions.UnusedSlot35.extension_clause D HW F ⟨p1, p8, hU⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LiftingTheoremWachModuleLemmaHypothesesAdmitted.lean:27 — `have h18 : LiftingTheory.adm18 D HW F := Formalism.MainNotions.UnusedSlot35.extension_invariant_clause D HW F ⟨p1, p8, p9, a, hU⟩`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalLiftingTheoremEHypothesesAdmitted.lean:29 — `Formalism.MainNotions.UnusedSlot35.extension_clause D HW F ⟨p1, p8, hX⟩,`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalLiftingTheoremEHypothesesAdmitted.lean:30 — `Formalism.MainNotions.UnusedSlot35.extension_invariant_clause D HW F ⟨p1, p8, p9, a, hX⟩⟩`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WachShiftMemOfExpansions.lean:92 — `have hU := Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit W h9 hA T hT`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WachShiftMemOfExpansions.lean:103 — `Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj W.π₀ hU (by rw [hrec k hk', uniformizer_smul_derivation W T hU]; rfl)`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/ExtensionClauses.lean:9 — `namespace Formalism.MainNotions.UnusedSlot35`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/ExtensionClauses.lean:41 — `end Formalism.MainNotions.UnusedSlot35`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/ExtensionInvariantClause.lean:7 — `namespace Formalism.MainNotions.UnusedSlot35.ExtCPf`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/ExtensionInvariantClause.lean:203 — `end Formalism.MainNotions.UnusedSlot35.ExtCPf`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/ExtensionInvariantClause.lean:205 — `namespace Formalism.MainNotions.UnusedSlot35`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/ExtensionInvariantClause.lean:210 — `Formalism.MainNotions.UnusedSlot35.ExtensionClassTheorem D HW F := by`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/ExtensionInvariantClause.lean:217 — `Formalism.MainNotions.UnusedSlot35.InvariantCocycleClassTheorem D HW F := by`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/ExtensionInvariantClause.lean:243 — `end Formalism.MainNotions.UnusedSlot35`
- `[ARROW(前件链)]` Formalism/SharpRestriction/LevelLetterCocycles/InvariantsGenerators.lean:90 — `Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm → SenOperatorLetter D HW F`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/SemisimpleLetterIffForallMem.lean:7 — `namespace Formalism.MainNotions.UnusedSlot35.DssRec`
- `[ARROW(前件链)]` Formalism/SharpRestriction/LevelLetterCocycles/SemisimpleLetterIffForallMem.lean:145 — `Formalism.MainNotions.UnusedSlot35.SemisimpleProductTheorem D HW F Cm ↔ (Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm →`
- `[ARROW(前件链)]` Formalism/SharpRestriction/LevelLetterCocycles/SemisimpleLetterIffForallMem.lean:158 — `Formalism.MainNotions.UnusedSlot35.SemisimpleLetterTheorem D HW F Cm ↔ (Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm →`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/SemisimpleLetterIffForallMem.lean:169 — `end Formalism.MainNotions.UnusedSlot35.DssRec`
- `[REF(引用)]` Formalism/SharpRestriction/LevelLetterCocycles/QuotientImageDivisibility/SmulSeriesDeltaZero.lean:308 — `have hπU := Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit W h9 hCA' T₁ hT₁`

### `UnusedSlot36`（14 处）

分类：REF(引用) 11，FIELD(结构字段) 2，ARROW(前件链) 1

- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean:7 — `namespace GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean:91 — `end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:18 — `open GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36 (algVal allVal ordVal Comb LeastLe Transfer TransferAt TransferInt TransferComb TransferLeast`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:119 — `(h : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) : Formalism.L2.PjFree.NoCommonZero Xo c w :=`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:126 — `(h : Formalism.L2.PjFree.NoCommonZero Xo c w) : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w := by`
- `[ARROW(前件链)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:199 — `(∀ k, w k ∈ cusp Xo c U aL nL) → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w →`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:257 — `Formalism.L2.PjFree.NoCommonZero Xo c w ↔ GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w :=`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:270 — `JointComb Xo c U (fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:271 — `JointLeast Xo c U (fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:273 — `(Formalism.L2.PjFree.NoCommonZero Xo c w ↔ GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) :=`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:283 — `Formalism.L2.PjFree.trivialClassCondition Xo c = GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.trivialClassCondition Xo c ∧ trivSet Xo c = ordVal Xo c ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:286 — `(Formalism.L2.PjFree.NoCommonZero Xo c w ↔ GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w)) ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:287 — `(regular₂ Xo c U ↔ JointInt Xo c U ∧ JointComb Xo c U (fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w) ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/NoCommonZeroIffOfSec.lean:288 — `JointLeast Xo c U (fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero w)) ∧`

### `UnusedSlot38`（30 处）

分类：REF(引用) 11，DEF 10，FIELD(结构字段) 5，SIGNATURE(槽) 4

- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedCompletionLemmas.lean:8 — `namespace Formalism.MainNotions.UnusedSlot38`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedCompletionLemmas.lean:883 — `end Formalism.MainNotions.UnusedSlot38`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:23 — `abbrev Pring : Subalgebra O (MvPowerSeries (Fin a) O) := Formalism.MainNotions.UnusedSlot38.Psub O (W wt)`
- `[FIELD(结构字段)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:30 — `(f : MvPowerSeries (Fin a) O) ∈ Formalism.MainNotions.UnusedSlot38.Pj O (W wt) (cj j)`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:33 — `(Formalism.MainNotions.UnusedSlot38.Pj O (W wt) (cj j)).comap (Pring O wt).val.toLinearMap`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:36 — `Formalism.MainNotions.UnusedSlot38.comp (W wt) (cj j) f`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:39 — `Formalism.MainNotions.UnusedSlot38.Pj_le_P (W wt) (W wt v) (Formalism.MainNotions.UnusedSlot38.X_mem_Pj (W wt) v)`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:201 — `def toA : PT O wt →ₐ[O] Formalism.MainNotions.UnusedSlot38.Asub (W wt) Jh :=`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:202 — `((Formalism.MainNotions.UnusedSlot38.mk Jh).comp (Pring O wt).val).codRestrict _ (fun f => ⟨f, f.2, rfl⟩)`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:213 — `def equivA : AT (PofJ wt Jh) ≃ₐ[O] Formalism.MainNotions.UnusedSlot38.Asub (W wt) Jh :=`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:219 — `def IsOl (O : Type) [CommRing O] (l : ℕ) : Prop := Formalism.MainNotions.UnusedSlot38.IsCoeff O l ∧ Irreducible (l : O)`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:268 — `def adm1 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := Formalism.MainNotions.UnusedSlot38.FiniteTypeRingPart`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LiftInvariantsFinrankEq.lean:305 — `namespace Formalism.MainNotions.UnusedSlot38`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LiftInvariantsFinrankEq.lean:326 — `end Formalism.MainNotions.UnusedSlot38`
- `[FIELD(结构字段)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:76 — `Q : Formalism.MainNotions.UnusedSlot38.AQuot P`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:91 — `def adm1 : Prop := ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => Formalism.MainNotions.UnusedSlot38.liftZP_unit T.P`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:93 — `def adm2 : Prop := Formalism.MainNotions.UnusedSlot38.FiniteTypeRingPart ∧ ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => Formalism.MainNotions.UnusedSlot38.UniversalLiftFiniteType T.P`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:95 — `def adm3 : Prop := Formalism.MainNotions.UnusedSlot38.PointsLemma D V`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:97 — `def ArchimedeanSignatureMatching : Prop := ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => Formalism.MainNotions.UnusedSlot38.LitG T.P → Formalism.MainNotions.UnusedSlot38.RelativePresentation T.P`
- `[SIGNATURE(槽)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:108 — `theorem first_hypothesis_of_lifting (h : Formalism.MainNotions.UnusedSlot38.Conclusion1 D V) : adm1 D V := fun _ _ _ _ _ _ _ _ _ T => h T.P`
- `[SIGNATURE(槽)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:109 — `theorem second_hypothesis_of_lifting (h : Formalism.MainNotions.UnusedSlot38.Conclusion2 D V) : adm2 D V := ⟨h.1, fun _ _ _ _ _ _ _ _ _ T => h.2 T.P⟩`
- `[SIGNATURE(槽)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:110 — `theorem integrality_of_commutation (h : Formalism.MainNotions.UnusedSlot38.PointsLemma D V) : adm3 D V := h`
- `[SIGNATURE(槽)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:111 — `theorem fourth_hypothesis_of_lifting (h : Formalism.MainNotions.UnusedSlot38.Conclusion5 D V) : ArchimedeanSignatureMatching D V :=`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:112 — `fun _ _ _ _ _ _ _ _ _ T hL => (Formalism.MainNotions.UnusedSlot38.lifting_lemma_of_literature h T.P hL).1`
- `[DEF]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/UnitaryThreeHeightBounds.lean:709 — `def lit2 : Prop := ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => Formalism.MainNotions.UnusedSlot38.LitG T.P`
- `[FIELD(结构字段)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/StrictlyAntitoneWeights/ConstantCoeffAtReducedPoint.lean:20 — `Jh_closed : Formalism.MainNotions.UnusedSlot38.IsClosedAdic Jh`
- `[FIELD(结构字段)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/StrictlyAntitoneWeights/ConstantCoeffAtReducedPoint.lean:21 — `Jh_hom : Formalism.MainNotions.UnusedSlot38.IsHomog (W P.wt) Jh`
- `[FIELD(结构字段)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/StrictlyAntitoneWeights/ConstantCoeffAtReducedPoint.lean:31 — `generator_mem_weight_ideal : ∀ i, eA.symm (X i) ∈ Formalism.MainNotions.UnusedSlot38.Aj (W P.wt) Jh (cj (wz i))`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/StrictlyAntitoneWeights/ConstantCoeffAtReducedPoint.lean:33 — `eA.symm (C (Ideal.Quotient.mk pt x)) ∈ Formalism.MainNotions.UnusedSlot38.Aj (W P.wt) Jh (cj j)`
- `[REF(引用)]` Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/StrictlyAntitoneWeights/ConstantCoeffAtReducedPoint.lean:48 — `T.eS (T.Q.q (Formalism.MainNotions.UnusedSlot38.resMap T.P v x))`

### `UnusedSlot39`（49 处）

分类：SIGNATURE(槽) 33，REF(引用) 9，FIELD(结构字段) 5，ARROW(前件链) 1，DEF 1

- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/HeckeValueIntegrality.lean:11 — `namespace GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/HeckeValueIntegrality.lean:86 — `end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CenUsedOfCenReal.lean:59 — `hkInt : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ParMem.lean:115 — `e18 : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeFrameIntAnyField.lean:26 — `open GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39 GlobalTheory.HkIntegral`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeOperatorPreservesSupLatticeRealSide.lean:33 — `theorem hkSupAt_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X :`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeOperatorPreservesSupLatticeRealSideStatement.lean:17 — `theorem _root_.GlobalTheory.T.heckeOperator_preserves_supLattice_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → Globa`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckePointIntegralUpToUnitsAnyAlgClosedField.lean:9 — `open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckePointIntegralUpToUnitsAnyAlgClosedField.lean:13 — `theorem heckeFrameInt_anyField_of : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckePointIntegralUpToUnitsAnyAlgClosedFieldStatement.lean:8 — `theorem _root_.GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw :`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeQuotientFrameChangeOfTriangularFrameChange.lean:75 — `theorem hkRelFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeQuotientFrameChangeOfTriangularFrameChangeStatement.lean:7 — `theorem _root_.GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.Inde`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeQuotientIntegralFramedPointCompleteField.lean:20 — `theorem heckeStable : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type)`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeQuotientIntegralFramedPointCompleteFieldStatement.lean:8 — `theorem _root_.GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InertiaEigenvalueTheoremOfHyp.lean:26 — `theorem exportF_isBuiltE : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerCha`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralCombIdempotentSectionsNonnegOverPlace.lean:11 — `open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralCombIdempotentSectionsNonnegOverPlaceStatement.lean:5 — `open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39`
- `[ARROW(前件链)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCDVRFractionFieldReadingInCpFiniteExtension.lean:116 — `GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCDVRFractionFieldReadingInCpFiniteExtensionStatement.lean:8 — `theorem _root_.GlobalTheory.T.isCDVRFractionFieldReadingInCp_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* `
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSplitHeckePrimeOffLevelOfHeckeIndexPlace.lean:15 — `GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime T0.Q.H T0.Q.l P.asIdeal (charAt P) ∧ charAt P ≠ D.ntw.l i := by`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSplitHeckePrimeOffLevelOfHeckeIndexPlaceStatement.lean:8 — `theorem _root_.GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace : ∀ (D : D7) (T0 : CoreJ D), LawsJ T0 → ∀ (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host), Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P → GlobalTheory.IndefiniteRowSideFull`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeriesRealizationOfPublished.lean:23 — `theorem exportAt_bundles : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → Gree`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SeriesRealizationOfPublishedStatement.lean:20 — `theorem _root_.GlobalTheory.T.series_realization_of_published : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Ge`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TheoremOfPublishedInputsStatement.lean:23 — `theorem _root_.GlobalTheory.T.theorem_of_published_inputs : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → `
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AutomorphyOfHyp.lean:33 — `theorem exportF_prmR : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → `
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AutomorphyOfPublishedInputsStatement.lean:27 — `theorem _root_.GlobalTheory.T.automorphy_of_hypotheses : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → Glo`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeckeIntegralityStatements.lean:16 — `GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform ∧ GlobalTheory.HeckeSupSt.HeckeReadTie :=`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeckeReadingEigenvaluePlace.lean:21 — `theorem ratHecke_keeps_ball : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → Glo`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeckeReadingEigenvaluePlaceStatement.lean:12 — `theorem _root_.GlobalTheory.T.hecke_reading_eigenvalue_place : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.Split`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LevelCharacterPsiCondition.lean:17 — `theorem intC_at_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalThe`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LevelCharacterPsiConditionStatement.lean:12 — `theorem _root_.GlobalTheory.T.level_character_psi_condition : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitO`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/BaseEmbeddingReadingEvalAdelicFunction.lean:237 — `theorem hkSupAt_of_readsCusp (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt) (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/BaseEmbeddingReadingEvalAdelicFunction.lean:424 — `theorem hkSupAt_of_clauses (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt) (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsLinearHeckeIsogenyInverseUpToPSq.lean:41 — `theorem exists_hkWith_of_hkRelFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H `
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsLinearHeckeIsogenyInverseUpToPSqStatement.lean:12 — `theorem _root_.GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRo`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnitNatCastUp.lean:47 — `open GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnitNatCastUp.lean:405 — `have a : HeckeFrameInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ _ _ => trivial`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransformIntegral.lean:152 — `theorem transform_integral (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeValueInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c))`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/TwistedOperators/TransformIntegral.lean:154 — `{P : Ideal (𝓞 E)} {p i : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p) (hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer Xo c P p i)`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/AutomorphyOfHyp.lean:27 — `theorem exportF_prmR_alt_alt : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEule`
- …（余 9 处，见脚本可重跑）

### `UnusedSlot55`（5 处）

分类：DEF(=True) 1，DEF 1，SIGNATURE(槽) 1，REF(引用) 1，PROVE-BY-TRIVIAL 1

- `[DEF(=True)]` Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean:89 — `def UnusedSlot55 {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (_ : NAut N) (_ : N.Loc) : Prop := True`
- `[DEF]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CuspidalGaloisUnramified.lean:33 — `def CuspidalGaloisUnramified' (D : D7) : Prop := ∀ i, _root_.UpperTheory.GalS.UnusedSlot55 D.nd D.naut i`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/NoG4Restrict.lean:10 — `theorem no_g4_restrict_alt {D : D7} {c : CutD D} (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (_ : ∀ i, UpperTheory.GalS.UnusedSlot55 D.nd D.naut i) :`
- `[REF(引用)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/NoG4Restrict.lean:11 — `∀ i, UpperTheory.GalS.UnusedSlot55 (cut D c).nd (cut D c).naut i := fun _ => trivial`
- `[PROVE-BY-TRIVIAL]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SClose.lean:24 — `(_ : JumpsCard D.nd D.naut) (i : D.nd.Loc) : UnusedSlot55 D.nd D.naut i := trivial`

### `UnusedSlot72`（12 处）

分类：SIGNATURE(槽) 5，FIELD(结构字段) 4，ARROW(前件链) 2，DEF(=True) 1

- `[FIELD(结构字段)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BernsteinUnitaryProductIrreducibleBis.lean:198 — `siegelEisensteinSimplePole : _root_.GlobalTheory.Published.UnusedSlot72`
- `[FIELD(结构字段)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BernsteinUnitaryProductIrreducibleTer.lean:64 — `siegelEisensteinSimplePole : _root_.GlobalTheory.Published.UnusedSlot72`
- `[DEF(=True)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7 — `abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DoublingMethodOfEisensteinFacts.lean:7 — `theorem _root_.GlobalTheory.T.doubling_zeta_of_eisenstein_facts : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIn`
- `[FIELD(结构字段)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/GeometricLemma.lean:73 — `siegelEisensteinSimplePole : _root_.GlobalTheory.Published.UnusedSlot72`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/MemberHodgeHypOfLocalInputsRationalWeights.lean:12 — `theorem member_hodgeHyp_of_localInputs_rationalWeights : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalThe`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/MemberHodgeHypOfLocalInputsRationalWeights.lean:22 — `theorem _root_.GlobalTheory.T.compatibleSystem_member_rationalWeights : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWall`
- `[ARROW(前件链)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSiegelWeilIdentityOfFormula.lean:13 — `GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 →`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSiegelWeilIdentityOfFormula.lean:25 — `theorem _root_.GlobalTheory.T.twisted_siegel_weil_identity : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCo`
- `[ARROW(前件链)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/TwistedSiegelWeilIdentityOfSiegelWeilFormula.lean:12 — `GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 →`
- `[FIELD(结构字段)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:74 — `siegelEisensteinSimplePole : _root_.GlobalTheory.Published.UnusedSlot72`
- `[SIGNATURE(槽)]` Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:505 — `theorem UpperTheory.LiteratureTheorems.siegel_eisenstein_simple_pole (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) : GlobalTheory.Published.UnusedSlot72 :=`

### `UnusedSlot80`（1611 处）

分类：REF(引用) 1256，FIELD(结构字段) 227，SIGNATURE(槽) 117，ARROW(前件链) 7，DEF 4

- `[ARROW(前件链)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleArcDatumGivesArcProperty.lean:11 — `UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm :=`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleArcDatumGivesArcProperty.lean:12 — `fun D HW F Cm hA h1f h11 => UnusedSlot80.arc_coordinates_final D HW F Cm hA h1f h11`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleArcDatumGivesArcPropertyStatement.lean:8 — `theorem _root_.GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → Ra`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:23 — `UnusedSlot80.SaturationArcLifting D HW F ∧ UnusedSlot80.SaturationEtale D HW F ∧ ArcLiftingSetup.SaturationFrobeniusPullback D HW F ∧ UnusedSlot80.GammaPreservesUniformiser D HW F ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:24 — `UnusedSlot80.KillerAtLevels D HW F ∧ UnusedSlot80.KillerBoundWithConstant D HW F 8 ∧ UnusedSlot80.KillerAtLevelsSecondForm D HW F ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:25 — `UnusedSlot80.FirstFiltrationArcLifting D HW F ∧ UnusedSlot80.FirstFiltrationEtale D HW F ∧ UnusedSlot80.SecondFiltrationArcLifting D HW F ∧ UnusedSlot80.SecondFiltrationEtale D HW F ∧`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:26 — `UnusedSlot80.FiltrationPropertiesEtale D HW F Cm ∧ UnusedSlot80.H1fBaseChangeFree D := by`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:31 — `have sA : UnusedSlot80.SaturationArcLifting D HW F := UnusedSlot80.saturation_general_statement D HW F ⟨p1, p9⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:32 — `have sE : UnusedSlot80.SaturationEtale D HW F := UnusedSlot80.saturation_unramified_statement D HW F ⟨p1, p9⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:33 — `have sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F := UnusedSlot80.saturation_pullback_statement D HW F p9`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:34 — `have pi : UnusedSlot80.GammaPreservesUniformiser D HW F := UnusedSlot80.gamma_uniformizer_divisible_statement D HW F p9`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:35 — `have kL : UnusedSlot80.KillerAtLevels D HW F := UnusedSlot80.annihilator_levels_unramified_statement D HW F Cm ⟨p4, p9⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:36 — `have kA : UnusedSlot80.KillerBoundWithConstant D HW F 8 := UnusedSlot80.killer_first_theorem_holds D HW F (le_refl _) ⟨kL, pi⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:37 — `have kE : UnusedSlot80.KillerAtLevelsSecondForm D HW F := UnusedSlot80.killer_second_theorem_holds D HW F pi`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:38 — `have f1A : UnusedSlot80.FirstFiltrationArcLifting D HW F := UnusedSlot80.firstFiltrationTheoremCaseA D HW F ⟨p2, p5, p9, a, hNat⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:39 — `have f1E : UnusedSlot80.FirstFiltrationEtale D HW F := UnusedSlot80.firstFiltrationTheoremEtale D HW F ⟨p2, p5, p9, a, hNat⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:40 — `have f2A : UnusedSlot80.SecondFiltrationArcLifting D HW F := UnusedSlot80.second_filtration_theorem_arc_lifting D HW F ⟨⟨p7, p9, b⟩, f1A⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:41 — `have f2E : UnusedSlot80.SecondFiltrationEtale D HW F := UnusedSlot80.cohomology_class_unramified_statement D HW F ⟨⟨p7, p9, b⟩, f1E⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:42 — `have tE : UnusedSlot80.FiltrationPropertiesEtale D HW F Cm := UnusedSlot80.tools_unramified_statement D HW F Cm ⟨p3, p4, p9⟩`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusions.lean:43 — `have bc : UnusedSlot80.H1fBaseChangeFree D := UnusedSlot80.base_change_statement D`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArcTheoremToolsOfWachModuleConclusionsStatement.lean:8 — `theorem _root_.GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.SaturationArcLifting D HW F ∧ UnusedSlot80.SaturationEtale D HW F ∧ ArcLiftingSetup.`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ClassSplittingAlongArcsOfAdmissible.lean:10 — `theorem classSplitAlongArcs : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLatti`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ClassSplittingAlongArcsOfAdmissible.lean:11 — `UnusedSlot80.split_case_A_final`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ClassSplittingAlongArcsOfAdmissibleStatement.lean:9 — `theorem _root_.GlobalTheory.T.classSplitting_along_arcs_of_admissible : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatt`
- `[ARROW(前件链)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrystallineUniversalPartCaseA.lean:12 — `UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D →`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrystallineUniversalPartCaseA.lean:13 — `UnusedSlot80.UniversalComponentCaseA D HW F Cm :=`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrystallineUniversalPartCaseA.lean:14 — `fun D HW F Cm hAdm h9 hH h15 => Formalism.MainNotions.UnusedSlot80.universal_general_statement_holds D HW F Cm hAdm h9 hH h15`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrystallineUniversalPartCaseAStatement.lean:8 — `theorem _root_.GlobalTheory.T.crystallineUniversalPart_caseA : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → Trun`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPointOverLetter.lean:26 — `have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPointOverLetter.lean:37 — `obtain ⟨g, hg⟩ := Formalism.MainNotions.UnusedSlot80.LevR.trans_prim (D.loc l) ((HW l).W K 1 LL hA.2.2)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPointOverLetter.lean:38 — `(Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA) hζ₁ _ hβ`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPointOverLetter.lean:71 — `refine Formalism.MainNotions.UnusedSlot80.LevR.level_condition_of_level_zero _ ((Cm l).C K 1 LL hA.2.2).tie.levB hs`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPointOverLetter.lean:83 — `exact Formalism.MainNotions.UnusedSlot80.LevR.lev0 _ T c ζ τ (Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le _ T c τ hover hsurj) h4'`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPointOverLetter.lean:98 — `have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPointOverLetter.lean:110 — `(by rw [pow_one]; exact (Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l).pow_eq_one)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExpansionRulesCriterionOddRootOfUnityCaseA.lean:26 — `haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExpansionRulesCriterionOddRootOfUnityCaseA.lean:28 — `haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL`
- `[FIELD(结构字段)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExpansionRulesCriterionOddRootOfUnityCaseA.lean:37 — `· have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA.2.2) :=`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExpansionRulesCriterionOddRootOfUnityCaseA.lean:38 — `(((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA.2.2))) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA.1)).1`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExpansionRulesCriterionOddRootOfUnityCaseA.lean:45 — `exact Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_of _ Subtype.val_injective hlm (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL)`
- …（余 1571 处，见脚本可重跑）

### `trivialClassCondition`（47 处）

分类：REF(引用) 33，SIGNATURE(槽) 11，DEF(=True) 3

- `[DEF(=True)]` Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean:14 — `def trivialClassCondition (T : CDVR) (ι : c.F →+* T.Fr) (_y : IntFr Xo c T ι) : Prop := True`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean:18 — `abbrev allVal (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) := valSet Xo c (trivialClassCondition Xo c) la`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/HeckeValueIntegrality.lean:36 — `def trivialClassCondition : PtClass Xo c := fun _ _ _ => True`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/HeckeValueIntegrality.lean:77 — `def HeckeIntAll : Prop := HeckeFrameInt Xo c (trivialClassCondition Xo c) ∧ HeckeValueInt Xo c (trivialClassCondition Xo c)`
- `[REF(引用)]` Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/HeckeValueIntegrality.lean:83 — `example (h : HeckeValueInt Xo c (trivialClassCondition Xo c)) : HeckeValueInt Xo c (goodCls Xo c) :=`
- `[REF(引用)]` Development/AbelianVarietyTheory/Definitions/RegularCharts/SCharts.lean:51 — `cover : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, ∃ (j : J) (V : Type) (_ : CommRing V) (_ : IsDomain V)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineCharts.lean:176 — `(h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v F := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineCharts.lean:209 — `∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineChartsStatement.lean:14 — `theorem _root_.GlobalTheory.T.integrality_trivialValuations_of_normalAffineCharts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SChar`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentreChart.lean:40 — `(h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v F := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentreChart.lean:78 — `∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentreChart.lean:217 — `∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ k, v (ws k)) ≤ (nu : EReal) := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsUnitOfVVEqZero.lean:29 — `(hl : LiesTotal Xo c (trivialClassCondition Xo c) PY lies)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsUnitOfVVEqZero.lean:36 — `OrdTieOn h δ (trivialClassCondition Xo c) PY lies := by`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsUnitOfVVEqZero.lean:93 — `theorem exists_frameShift_ordTies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) `
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsUnitOfVVEqZero.lean:117 — `theorem ordTies_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ [Fintype (Comp (Q.Xo j) Q.c)] (h : GenFrEx (Q.Xo j) Q.c), KapFG (Q.Xo j) Q.c ∧ (∃ d, KapTrdeg (Q.Xo j) Q.c d ∧ d + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j) ∧ FnTrdeg (Q.X`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsUnitOfVVEqZero.lean:124 — `have hl : LiesTotal (Q.Xo j) Q.c (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/HeightInequalitiesIndefiniteLiftIndex.lean:172 — `(hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/HeightInequalityDefiniteLiftIndex.lean:206 — `(hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/HeightInequalityDefiniteLiftIndex.lean:238 — `(hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/LengthsAtPrimesLeFunctionFieldDataOfCurve.lean:517 — `theorem ilaTie_of_curveHyp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toL`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/LengthsAtPrimesLeFunctionFieldDataOfCurveStatement.lean:15 — `theorem _root_.GlobalTheory.T.lengths_at_primes_le_functionField_data_of_curve : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyD`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/OrdersAuxiliaryFormAtPrimesEqFunctionField.lean:326 — `theorem netTie_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCo`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/OrdersAuxiliaryFormAtPrimesEqFunctionFieldStatement.lean:15 — `theorem _root_.GlobalTheory.T.orders_auxiliary_form_at_primes_eq_functionField : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyD`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/OrdTiesOfPins.lean:29 — `(hl : LiesTotal Xo c (trivialClassCondition Xo c) PY lies)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/OrdTiesOfPins.lean:36 — `OrdTieOn h δ (trivialClassCondition Xo c) PY lies := by`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/OrdTiesOfPins.lean:95 — `theorem exists_frameShift_ordTies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) `
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/OrdTiesOfPins.lean:119 — `theorem ordTies_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ [Fintype (Comp (Q.Xo j) Q.c)] (h : GenFrEx (Q.Xo j) Q.c), KapFG (Q.Xo j) Q.c ∧ (∃ d, KapTrdeg (Q.Xo j) Q.c d ∧ d + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j) ∧ FnTrdeg (Q.X`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/OrdTiesOfPins.lean:126 — `have hl : LiesTotal (Q.Xo j) Q.c (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) := by`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/RealisationValuesEqValuedPointOrders.lean:217 — `(ev : ∀ w, M w → U.Fr) (p : valSet Xo c (trivialClassCondition Xo c) la)`
- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/RealisationValuesEqValuedPointOrders.lean:224 — `(hδ : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) :`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/RealisationValuesEqValuedPointOrders.lean:362 — `theorem GlobalTheory.RealisationValues.values_eq_orders : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka`
- `[SIGNATURE(槽)]` Development/AbelianVarietyTheory/Proofs/HeightProofs/RealisationValuesEqValuedPointOrdersStatement.lean:15 — `theorem _root_.GlobalTheory.T.realisation_values_eq_valuedPoint_orders : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (rec`
- `[REF(引用)]` Formalism/LocalToGlobal/ProjectiveLattices/FreeBridge.lean:100 — `trivialClassCondition Xo c T ι y ↔ Formalism.L2.Pj.trivialClassCondition Xo c T ι y := by rfl`
- `[REF(引用)]` Formalism/LocalToGlobal/ProjectiveLattices/IntAtExtExtAll.lean:13 — `Pt' la := valSet (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) la`
- `[REF(引用)]` Formalism/LocalToGlobal/ProjectiveLattices/NumericalH1Condition.lean:107 — `let y1 : PtV Xo c (trivialClassCondition Xo c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho z trivial () trivial`
- `[REF(引用)]` Formalism/LocalToGlobal/ProjectiveLattices/RealPtMain.lean:90 — `let yV : PtV (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho y trivial () trivial`
- `[DEF(=True)]` Formalism/LocalToGlobal/ProjectiveLattices/RegPFree.lean:16 — `def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True`
- `[REF(引用)]` Formalism/LocalToGlobal/ProjectiveLattices/RegPFree.lean:19 — `valSet Xo c (algCls Xo c) la ⊆ valSet Xo c (trivialClassCondition Xo c) la := by`
- `[REF(引用)]` Formalism/LocalToGlobal/ProjectiveLattices/RegPFree.lean:35 — `(fun la => valSet Xo c (algCls Xo c) la) (fun la => valSet Xo c (trivialClassCondition Xo c) la)`
- …（余 7 处，见脚本可重跑）

### `⟨UnusedSlot80`（1 处）

分类：REF(引用) 1

- `[REF(引用)]` Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WachRelayLemmaArcCoordinateHypotheses.lean:20 — `exact ⟨UnusedSlot80.relay_general_statement D HW F ⟨p5, p9, hH, hTr, hSat, hF1, hF2⟩,`
