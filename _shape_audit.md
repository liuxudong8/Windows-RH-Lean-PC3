# 形状清单 v2：Band / RvM 族 + 未证形状（带消费判决）

- 生成 2026-11-25 06:12　根 `C:\proj2`（排除 `.lake`、`_probe*`）
- 声明 **2611**；`def : Prop` **104**；其中**孤立形状 42**、有消费者 62

## 表 A　Band / RvM 族（7 条）

| 文件 | 行 | 类别 | 名字 | Prop | 引用 | 状态 |
|---|---|---|---|---|---|---|
| QRH/S7_1_Main.lean | 1266 | def | `physDeltaRvM` | 否 | — | 定义件 |
| QRH/S7_1_Main.lean | 1269 | def | `physWindowRvM` | 否 | — | 定义件 |
| QRH/S7_1_Main.lean | 1274 | theorem | `physDelta_sub_physDeltaRvM` | 否 | — | 已证 |
| QRH/S7_1_Main.lean | 1295 | def | `pairConstantRvM` | 否 | — | 定义件 |
| QRH/S7_1_Main.lean | 1304 | def | `PairBandRvM` | 是 | 1 | **未证形状** |
| QRH/S7_1_Main.lean | 1308 | theorem | `physDeltaRvM_le_physDelta` | 否 | — | 已证 |
| QRH/S7_1_Main.lean | 1318 | theorem | `physDeltaRvM_pos` | 否 | — | 已证 |

## 表 B1　孤立形状（42 条，**无证明、无消费者**）

| 文件 | 行 | 名字 |
|---|---|---|
| OrderPreservingBijection/EllipticClasses.lean | 38 | `matrixDet` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 18 | `LogDerivSeries` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 23 | `PsiZeroConst` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 27 | `SmoothedRemainderLipschitz` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 33 | `SmoothedRemainderRealLipschitz` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 39 | `ZeroFreeSymmetric` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 44 | `ZeroSumBoundSmall` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 53 | `ZeroSumBoundLarge` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 61 | `PartialSumIntegralBound` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 79 | `ShortIntervalImpliesProgressions` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 83 | `KronOdd` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 86 | `KronTwo` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 89 | `ClassConst` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 96 | `JacobiInOut` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 100 | `LamSumZero` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 104 | `MuConst` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 110 | `MuSmall` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 116 | `MeanRemove` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 128 | `SizeSumC` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 132 | `SizeSpAll` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 135 | `SizeSpLarge` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 138 | `SizeR` |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 144 | `SizeSpSq` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 27 | `SmoothedRemainderIntegralFormula` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 34 | `SmoothedRemainderRealIntegralFormula` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 42 | `WeightedSumTendsto` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 49 | `SmoothedRemainderHasDerivBound` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 56 | `SmoothedRemainderRealHasDerivBound` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 65 | `SmoothedRemainderScaling` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 70 | `SmoothedRemainderScaledDiffBound` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 75 | `SmoothedRemainderRealScaledDiffBound` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 93 | `ExceptionalCharacterCountBound` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 98 | `TailSumBound` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 141 | `PrimesInProgressionCountLowerBound` |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 155 | `JacobiTwistedMeanSquareBound` |
| OrderPreservingBijection/Exceptional/Statement.lean | 20 | `ZFRDirichlet` |
| OrderPreservingBijection/Exceptional/ZerosDisc.lean | 25 | `derSeries` |
| OrderPreservingBijection/Exceptional/ZerosDisc.lean | 28 | `primesIoc` |
| OrderPreservingBijection/Exceptional/ZerosDisc.lean | 30 | `psiAP` |
| OrderPreservingBijection/Exceptional/ZerosDisc.lean | 41 | `PrimesRel` |
| OrderPreservingBijection/QuadraticFieldFive.lean | 1143 | `IsRamified` |
| QRH/S7_1_Main.lean | 1304 | `PairBandRvM` |

## 表 B2　有消费者的 `def : Prop`（62 条，谓词/已被用）

| 文件 | 行 | 名字 | 引用数 |
|---|---|---|---|
| A5CharQ5/A5Defs.lean | 1367 | `S` | 637 |
| QRH/S7_1_Main.lean | 64 | `pairConstant` | 38 |
| OrderPreservingBijection/SylvesterInertia.lean | 46 | `Jpq` | 33 |
| OrderPreservingBijection/ZetaZeros.lean | 1185 | `IsFarZero` | 23 |
| BSD/LeibnizReduction.lean | 62 | `C2At` | 19 |
| OrderPreservingBijection/stage_4.lean | 3045 | `UniformSupport` | 18 |
| OrderPreservingBijection/SylvesterInertia.lean | 50 | `HasSignature` | 17 |
| OrderPreservingBijection/stage_3.lean | 130 | `UnitEquiv` | 17 |
| OrderPreservingBijection/Interpolation.lean | 44 | `PointSetSeparable` | 16 |
| QRH/S7_1_Main.lean | 69 | `WeakRealPart` | 15 |
| OrderPreservingBijection/stage_4.lean | 6042 | `ADefiniteSignature` | 14 |
| OrderPreservingBijection/Exceptional/ZerosDisc.lean | 32 | `IsExc` | 12 |
| QRH/S7_1_Main.lean | 1350 | `KernelAdmissible` | 12 |
| BSD/LeibnizThird.lean | 26 | `C3At` | 11 |
| OrderPreservingBijection/QuadraticFieldFive.lean | 1146 | `IsSplit` | 11 |
| OrderPreservingBijection/stage_3.lean | 82 | `IsNonUnit` | 11 |
| OrderPreservingBijection/SylvesterInertia.lean | 42 | `cT` | 10 |
| OrderPreservingBijection/stage_3.lean | 165 | `HyperbolicEquiv` | 10 |
| QRH/S7_1_Main.lean | 1680 | `BGSLocalUniform` | 10 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 21 | `Gchi` | 9 |
| OrderPreservingBijection/stage_3.lean | 124 | `elementTrace` | 9 |
| QRH/S7_1_Stage3.lean | 52 | `Bound` | 9 |
| OrderPreservingBijection/stage_3.lean | 350 | `IsPrimeElement` | 8 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 24 | `Gone` | 7 |
| OrderPreservingBijection/QuadraticFieldFive.lean | 673 | `has_unit_form` | 7 |
| OrderPreservingBijection/stage_3.lean | 77 | `IsPrimitive` | 7 |
| QRH/S7_1_Main.lean | 55 | `ZeroSet` | 7 |
| QRH/S7_1_Main.lean | 1701 | `DiagRate` | 7 |
| QRH/S7_1_Stage3.lean | 56 | `BoundBall` | 7 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 113 | `Emain` | 6 |
| OrderPreservingBijection/ManifoldInfrastructure.lean | 552 | `GammaEquiv` | 6 |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 121 | `sP` | 5 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 115 | `rhoErr` | 5 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 147 | `cn` | 5 |
| OrderPreservingBijection/QuadraticFieldFive.lean | 1149 | `IsInert` | 5 |
| OrderPreservingBijection/stage_4.lean | 774 | `ContinuousTermRegular` | 5 |
| BSD/ShaFreeLayer.lean | 77 | `Nondegenerate` | 4 |
| OrderPreservingBijection/BijectionPhi/Basic.lean | 68 | `NonUnitAlgebra` | 4 |
| OrderPreservingBijection/EllipticClasses.lean | 35 | `matrixTrace` | 4 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 19 | `psumR` | 4 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 149 | `outPart` | 4 |
| OrderPreservingBijection/QuadraticFieldFive.lean | 1140 | `discriminant` | 4 |
| BSD/Sha11_389.lean | 33 | `ShaFinite` | 3 |
| OrderPreservingBijection/BijectionPhi/Basic.lean | 80 | `PrimitiveElement` | 3 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 80 | `GoodFor` | 3 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 111 | `Li` | 3 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 132 | `PrimesAPInterval` | 3 |
| OrderPreservingBijection/Exceptional/Statement.lean | 14 | `InRegion` | 3 |
| OrderPreservingBijection/Exceptional/Statement.lean | 17 | `IsLZero` | 3 |
| OrderPreservingBijection/EllipticClasses.lean | 42 | `IsEllipticMatrix` | 2 |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 72 | `PrimeCountAsymptoticInProgressions` | 2 |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 93 | `inPart` | 2 |
| OrderPreservingBijection/Exceptional/PrimeCountAsymptoticInProgressions.lean | 124 | `Rsum` | 2 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 83 | `ZeroPairs` | 2 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 87 | `ZeroDensityBound` | 2 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 90 | `BadChars` | 2 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 118 | `ShortIntervalLowerBound` | 2 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 138 | `PP` | 2 |
| OrderPreservingBijection/Exceptional/SmoothedRemainderRealIntegralFormula.lean | 152 | `sqSum` | 2 |
| OrderPreservingBijection/Exceptional/ZerosDisc.lean | 37 | `ExcData` | 2 |
| OrderPreservingBijection/stage_3.lean | 438 | `IsPrimeIdeal` | 2 |
| QRH/S7_1_Main.lean | 58 | `ConjClosed` | 2 |

## 判读

- **孤立形状** = 名字在整库只出现一次（即声明行本身）。它既没有证明，也没有任何定理引用它 ⟹ 对证明系统零贡献，只占一个名字。**这才是「未证形状」的危险区。**
- 有消费者 = 至少被引用过一次，通常是合法谓词（`IsEllipticMatrix` 这类），是定理陈述的组成部分，不算问题。
- 引用计数是静态文本匹配，不含动态解析；同名不同文件会合并计数（粗筛够用，精确需 Lean 侧 `#check`）。
- **假设/黑箱**（`axiom` / `opaque`）不在本清单，它们进闭包、是账本条目。
