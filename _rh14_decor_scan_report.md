# RH_14 归档 · 装饰壳静态扫描（第 1 步）

扫描根：`F:\F\BSD_GRH_RH\RH_14\lean\src`

- `.lean` 文件：**175187**（读盘失败 0）
- `theorem` / `lemma`：**748758**
- 薄壳（body 为单个常量）：**28224**，其中带显式 binder：**19865**
- 零字段 `structure … : Prop where`：**0**

判定口径：对每个「消费 gate 的薄壳定理」，查其**引用常量的类型**里是否出现该 gate。
不出现 → `DECO`（该假设在此定理内结构上不可能被消费）；出现 → `PASS`；
引用者在库外（Mathlib 侧）→ `UNKNOWN`；body 不是单常量 → `NO-REF`。

## 汇总

| gate | 消费处 | 装饰 DECO | 传递 PASS | 外部 UNKNOWN | 非薄壳 |
|---|---|---|---|---|---|
| `Green` | 4 | **0** | 3 | 1 | 0 |
| `Hyps` | 2 | **0** | 0 | 2 | 0 |
| `EveryCharacter` | 1 | **0** | 1 | 0 | 0 |
| `OpenLiteratureStatements` | 129 | **126** | 0 | 3 | 0 |
| `RecTExists` | 9 | **1** | 6 | 2 | 0 |
| `TLiftK` | 1 | **1** | 0 | 0 | 0 |
| `RiemannHypothesis` | 2 | **0** | 1 | 1 | 0 |

总计：DECO **128** / PASS **11** / UNKNOWN **9**

## 装饰样例（前 60）

- `TLiftK` — `Development\AutomorphicArithmetic\Foundations\GaloisRepresentations\ThetaParseval\ThetaKernels\TLiftK.lean:4` `UpperTheory.TP.K.tLiftK := UpperTheory.TP.tLift_holds_k`
- `RecTExists` — `Development\AutomorphicArithmetic\Foundations\UnitarySphericalFixing\SatakeParameters\AbsCentral.lean:85` `abConv := H`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:219` `UpperTheory.LiteratureTheorems.logDerivOne := GlobalTheory.LogDerOneProof.logDerOne_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:221` `UpperTheory.LiteratureTheorems.ellipticMainTheoremCM' := PositivityTheory.Prw.ellipticMainTheoremCM_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:223` `UpperTheory.LiteratureTheorems.heckeTateFunctionalEquation' := GlobalTheory.Top.heckeTateFE`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:225` `UpperTheory.LiteratureTheorems.hilbertClassFieldJ' := GlobalTheory.Laid.hcfj_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:227` `UpperTheory.LiteratureTheorems.partial_zeta_functional_equation_of_literature := PositivityTheory.Prw.partialZetaFunctionalEquation_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:229` `UpperTheory.LiteratureTheorems.deligne_ribet_of_literature := PositivityTheory.PfDR.deligneRibet_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:237` `UpperTheory.LiteratureTheorems.ab_mul_n_st_of_literature := GlobalTheory.abMulN_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:239` `UpperTheory.LiteratureTheorems.abelian_de_rham_of_literature := PositivityTheory.DualRT.abelianDeRham`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:241` `UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_literature := GlobalTheory.deRham_potentiallySemistable`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:243` `UpperTheory.LiteratureTheorems.global_artin_reciprocity_of_literature := GlobalTheory.globalArtinReciprocity_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:245` `UpperTheory.LiteratureTheorems.hecke_l_adic_character_de_rham_of_literature := UpperTheory.Lit.heckeLAdicCharacterDeRham`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:253` `UpperTheory.LiteratureTheorems.principalisation_of_literature := PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:257` `UpperTheory.LiteratureTheorems.automorphic_forms_finite_gl_of_literature := CuspFormAutomorphicBounds.automorphicFormsFiniteGL`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:259` `UpperTheory.LiteratureTheorems.base_change_isobaric := UpperTheory.BaseChangeIdentities.baseChangeN`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:263` `UpperTheory.LiteratureTheorems.bernstein_unitary_product_irreducible_of_literature := PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:265` `UpperTheory.LiteratureTheorems.bernstein_zelevinsky_finiteness_of_literature := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:267` `UpperTheory.LiteratureTheorems.bhatt_scholze_integral_of_literature := GlobalTheory.BSP.bhattScholzeIntegral`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:271` `UpperTheory.LiteratureTheorems.bloch_kato_local_of_literature := UpperTheory.Lit.blochKatoLocal`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:273` `UpperTheory.LiteratureTheorems.borel_casselman_of_literature := PositivityTheory.Stage1.PM.borelCasselman`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:277` `UpperTheory.LiteratureTheorems.cm_curve_good_outside_prime_st_of_literature := GlobalTheory.Published.cmCurveGoodOutsidePrime`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:281` `UpperTheory.LiteratureTheorems.local_converse_gl_of_literature := DiscreteGroups.sglob.LConv.localConverseGL`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:289` `UpperTheory.LiteratureTheorems.jacquet_shalika_rigidity_of_literature := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:297` `UpperTheory.LiteratureTheorems.geometric_restriction_of_literature := GlobalTheory.CompanionTheory.GeoLink.geometricLemma`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:301` `UpperTheory.LiteratureTheorems.segment_representation_of_literature := PositivityTheory.RgGu.segmentRepresentation`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:315` `UpperTheory.LiteratureTheorems.irreducible_admissible_gl_of_literature := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:317` `UpperTheory.LiteratureTheorems.standard_functors_finite_length_of_literature := PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:321` `UpperTheory.LiteratureTheorems.casselman_wallach_of_literature := PositivityTheory.CWB.casselmanWallach`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:325` `UpperTheory.LiteratureTheorems.chow_form_exists_of_literature := GlobalTheory.Published.chowFormExists_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:327` `UpperTheory.LiteratureTheorems.clozel_cohomological_of_literature := PositivityTheory.Rg.Cz.clozelCohomological`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:329` `UpperTheory.LiteratureTheorems.clozel_purity_of_literature := PositivityTheory.Lit1.ClozelPurity.clozelPurity`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:331` `UpperTheory.LiteratureTheorems.complex_multiplication_j_st_of_literature := GlobalTheory.CompanionTheory.Published.complexMultiplicationJ`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:333` `UpperTheory.LiteratureTheorems.cusp_bounded_of_literature := PositivityTheory.Stage1.PM.cuspBounded`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:337` `UpperTheory.LiteratureTheorems.cusp_decay_sobolev_of_literature := PositivityTheory.Stage1.PM.cuspDecaySobolev`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:343` `UpperTheory.LiteratureTheorems.cuspidal_mirabolic_of_literature := GlobalTheory.cuspidalMirabolic_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:345` `UpperTheory.LiteratureTheorems.cuspidal_spectrum_gl_of_literature := RfCs.cuspidalSpectrumGL`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:351` `UpperTheory.LiteratureTheorems.depth_zero_support_of_literature := GlobalTheory.SmGL.depthZeroSupport`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:353` `UpperTheory.LiteratureTheorems.discrete_series_classification_of_literature := CompanionTheory.RgExh.discreteSeriesClassification`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:355` `UpperTheory.LiteratureTheorems.discrete_series_cover_of_literature := CompanionTheory.RgExh.discreteSeriesCover`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:357` `UpperTheory.LiteratureTheorems.discrete_series_cover_exists_of_literature := CompanionTheory.RgDs.B.discreteSeriesCoverExists`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:359` `UpperTheory.LiteratureTheorems.discrete_series_exists_of_literature := CompanionTheory.RgDs.B.discreteSeriesExists`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:361` `UpperTheory.LiteratureTheorems.discrete_series_hermitian_unique_of_literature := PositivityTheory.Prw.discreteSeriesHermitianUnique_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:363` `UpperTheory.LiteratureTheorems.discrete_series_lowest_k_type_of_literature := PositivityTheory.Prw.discreteSeriesLowestKType_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:365` `UpperTheory.LiteratureTheorems.discrete_series_upq_exists_of_literature := CompanionTheory.RgDs.B.discreteSeriesUpqExists`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:367` `UpperTheory.LiteratureTheorems.dixmier_malliavin_factorisation_of_literature := GlobalTheory.dixmierMalliavinFactorisation_fromLibrary`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:369` `UpperTheory.LiteratureTheorems.siegel_eisenstein_continuation_of_literature := PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:373` `UpperTheory.LiteratureTheorems.flath_tensor_product_of_literature := CompanionTheory.Rg.Fl.B.flathTensorProduct`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:375` `UpperTheory.LiteratureTheorems.unitary_irreducible_admissible_of_literature := CompanionTheory.Rg.Fl.B.unitaryIrreducibleAdmissible`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:381` `UpperTheory.LiteratureTheorems.formal_algebraisation_of_literature := PositivityTheory.FormalThickening.formalAlgebraisation`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:383` `UpperTheory.LiteratureTheorems.formal_degree_compact_dual_of_literature := PositivityTheory.RgFd.B.formalDegreeCompactDual`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:385` `UpperTheory.LiteratureTheorems.gk_globalisation_of_literature := GlobalTheory.gkGlobalisation_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:387` `UpperTheory.LiteratureTheorems.gl_howe_duality_of_literature := PositivityTheory.Stage1.PM.gLHoweDuality`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:391` `UpperTheory.LiteratureTheorems.generic_unitary_dual_gl_of_literature := PositivityTheory.Gud.Fin.genericUnitaryDualGL_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:393` `UpperTheory.LiteratureTheorems.geometric_restriction_filtration_of_literature := GlobalTheory.geometricLemmaFiltration_holds`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:395` `UpperTheory.LiteratureTheorems.good_chern_weil_of_literature := GlobalTheory.GoodMetric.goodChernWeil`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:397` `UpperTheory.LiteratureTheorems.green_cuspidal_of_literature := PositivityTheory.Stage1.PM.greenCuspidal`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:399` `UpperTheory.LiteratureTheorems.green_regular_characters_of_literature := PositivityTheory.Stage1.PM.greenRegularCharacters`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:403` `UpperTheory.LiteratureTheorems.abelian_lifting_of_literature := GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers`
- `OpenLiteratureStatements` — `Development\AutomorphicArithmetic\ThetaCorrespondence\ThetaPairLifts\ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:409` `UpperTheory.LiteratureTheorems.principal_polarisation_one_section_of_literature := GlobalTheory.AbLaw.principalPolarisation_unique_section`
