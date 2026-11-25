# RH_14 · `*_holds` 节点与真空槽计数（纯静态）

根：`F:\F\BSD_GRH_RH\RH_14\lean\src`（175187 个 `.lean`）

## 一、`*_holds` 规模

- 声明总数（含 `theorem/lemma/def/abbrev/opaque`）：**5659**
- 去重后名字数：**5308**
- 其中 `def … : Prop :=` 形态：**16**
- 按声明种类：`theorem` 5657，`def` 1，`lemma` 1

按顶层目录：

- `Formalism`：3109
- `Development`：2155
- `ReciprocityTheory`：202
- `PositivityTheory`：99
- `GroundTheory`：63
- `CompanionTheory`：31

## 二、真空槽规模

- `: Prop := True` 命中：**11**
- `UnusedSlot* / NoCondition*` 定义：**2**

- `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean:89` — `def UnusedSlot55 {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (_ : NAut N) (_ : N.Loc)`
- `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean:90` — `def NoCondition (_ : D7) : Prop :=`

## 三、`*_holds` 抽样（前 30）

- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/CoefWeightedLocHolds.lean:17 — `CoefWeightedLoc_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/CoefWeightedLocHolds.lean:19 — `BesselNVGap_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/CoefWeightedLocHolds.lean:21 — `WlocExists_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/CoefWeightedLocHolds.lean:23 — `NUnimodLoc_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/CoefWeightedLocHolds.lean:28 — `QuotProdK_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/DoubleCosetBesselBoundOfGapConstantLe.lean:22 — `besselOfW_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/EClose.lean:17 — `locQuadGG_G_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/EFinal.lean:15 — `stepIntG_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/EFinal.lean:19 — `weilPairJ_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/LocQuad1GHolds.lean:19 — `locQuad1_G_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/LocQuad1GHolds.lean:128 — `stepConvG_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/MultiplicityOneUnitaryBranchingOfGapHyp.lean:8 — `uniqGap_holds`
- `theorem` CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/MultiplicityOneUnitaryBranchingOfGapHyp.lean:10 — `ampUnif_holds`
- `theorem` CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DixmierMalliavinFactorisationHolds.lean:104 — `CompanionTheory.DM.dixmierMalliavinFactorisation_holds`
- `theorem` CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/UnitarySiegelSets/SiegelSetUnitaryHolds.lean:9 — `siegelCore_holds`
- `theorem` CompanionTheory/AutomorphicTheory/ProductFormulaTheory/DualAbelianSchemes/Rigdesc.lean:14 — `rigDescent_holds`
- `theorem` CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/JacquetFunctionalNormalization.lean:17 — `inputs_holds`
- `theorem` CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/JacquetFunctionalNormalization.lean:20 — `rankOne_holds`
- `theorem` CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/Transfer.lean:270 — `transfer_holds`
- `theorem` CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/EquivariantSections/KeyIdentityHolds.lean:16 — `key_identity_holds`
- `theorem` CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/HilbertSpaceModels/HilbertSignatureHolds.lean:12 — `hilbert_signature_holds`
- `theorem` CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/HilbertSpaceModels/HilbertSpaceRealisationHolds.lean:16 — `hilbert_space_realisation_holds`
- `theorem` CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/HilbertSpaceModels/HilbertStableHolds.lean:10 — `hilbert_stable_holds`
- `theorem` CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/HilbertSpaceModels/HilbertStableHolds.lean:17 — `hilbert_datum_holds`
- `theorem` CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/RhoRepresentations/EquivSection.lean:9 — `equivariant_section_holds`
- `theorem` CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/RhoRepresentations/RhoRep.lean:47 — `rho_representation_holds`
- `theorem` CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HenselStatement.lean:8 — `stHensel_holds`
- `theorem` CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InnerEqZeroOfWeight.lean:240 — `lowSpan_holds`
- `theorem` CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZuckermanHypothesis.lean:94 — `zuckerman_hypothesis_holds`
- `theorem` CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean:153 — `localLift_holds`