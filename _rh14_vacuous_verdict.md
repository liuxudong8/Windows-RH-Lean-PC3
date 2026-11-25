# RH_14 真空命题 · 逐消费点判定（第 2 条结项）

根：`F:\F\BSD_GRH_RH\RH_14\lean\src`
脚本：`_rh14_vacuous_sites.py`（扫描）＋ `_rh14_sites2.py`（承载点定位）

## 0. 先纠账：11 条里 3 条是误报

扫描器用 `: Prop := True` 作模式，会命中**以 `True` 开头的标识符**与**换行后的 `True ∧ …`**：

| 名字 | 实际定义 | 性质 |
|---|---|---|
| `CanE` | `TrueF D ∧ BigGap D` | **真内容**，误报 |
| `SettingHypotheses` | `True ∧ (∀ s, DualLat ∧ NoJump) ∧ …` | **真内容**，误报 |
| `SetHyp` | `True ∧ (∀ s, goodS → SelfDual) ∧ … ∧ 100 ≤ D.R.r ∧ …` | **真内容**，误报 |

另有 4 个 `UnusedSlot33/34/38/80` 不是命题而是**命名空间**（`UnusedSlot80.ToolsR.RingP`、`UnusedSlot38.Asub`、`UnusedSlot34.ForAllCM` 等），
`UnusedSlot80` 那 1,611 处命中是命名空间引用，与真空无关。此项撤回。

**净剩真真空：6 个名字 / 8 处定义。**

## 1. 六个真空命题与判定

| 名字 | 定义处 | 消费点 | 名字是否承诺内容 | 判定 |
|---|---|---|---|---|
| `GlobalTheory.Published.UnusedSlot72` | `LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`（`abbrev … : Prop := True`） | 12 处：结构字段 4、槽 5、前件链 2、定义 1 | **承诺**（使用处挂名 `siegelEisensteinSimplePole`） | **真洞** |
| `UnusedSlot55` | `TypeConditions/TrivialLocalCondition.lean:89` | 5 处 | 否（编号槽） | 合法占位 |
| `NoCondition` | `TypeConditions/TrivialLocalCondition.lean:90` | 5 处 | 否（名即"无条件"） | 合法 |
| `UpperTheory.One.M.TrivialCondition` | `SatakeParameters/SwOn.lean:5` | 16 处（槽 8） | 否 | 合法，但属典型装饰参数 |
| `TrivialRankCondition` | `LatticeFrames/NotInhAbsOfGamLe.lean:36` | 3 处 | 否 | 合法 |
| `trivialClassCondition`（Prop 版） | `OrderValuation.lean:14`、`RegPFree.lean:16`、`ValSetAlgSubset.lean:14`（3 份拷贝） | 47 处 | 否 | 合法；另有 `PtClass` 版（`HeckeValueIntegrality.lean:36 def … : PtClass := fun _ _ _ => True`）是**取平凡理想类**的真参数，非真空 |

## 2. `UnusedSlot72`：唯一"名字承诺、定义给 True"的洞

四层证据，全部已核行号：

1. 定义：`abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True`。
2. 挂名做结构字段，字段名承诺一个具体解析事实：
   - `LocalTypeDictionary/GeometricLemma.lean:73` — `siegelEisensteinSimplePole : _root_.GlobalTheory.Published.UnusedSlot72`
   - `BernsteinUnitaryProductIrreducibleBis.lean:198`、`…Ter.lean:64`、`ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:74` — 同名字段
3. 作为前件进主链：
   - `TwistedSiegelWeilIdentityOfFormula.lean:13` 与 `:25`
   - `TwistedSiegelWeilIdentityOfSiegelWeilFormula.lean:12`
   - `DoublingMethodOfEisensteinFacts.lean:7`（`doubling_zeta_of_eisenstein_facts` 的第 3 前件）
4. 供货：`ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:505`
   `siegel_eisenstein_simple_pole (O : OpenLiteratureStatements) : UnusedSlot72 := trivial`
   ——`O` 在证明项里不出现，第 1 步已判 DECO。

逻辑后果（必须写清）：`H → C` 且 `H := True` ⟹ `C` **无条件成立**。
所以这不是"循环"，是**空洞**：结论比原意强，强出来的部分（"Siegel 艾森斯坦级数有简单极点"）没有证明，只是被 `True` 顶掉。

## 2.5 `siegelEisensteinSimplePole` 往下追：进了 root 的第一实参，但没有被读

链路（行号已核）：

1. `EveryCharacterOfLiteratureOfVWin.lean:666` `theorem published_results_eigen (O) : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses where`（字段 667–726 共 60 个）；
2. `:718` `siegelEisensteinSimplePole := (_root_.UpperTheory.LiteratureTheorems.siegel_eisenstein_simple_pole O)`——其值即 `trivial`（见 `:505`）；
3. `EveryCharacterOfLiteratureOfVWin.lean:811` root 体**第一实参**就是 `published_results_eigen O`；
4. 接收方 `SiegelEisensteinSecondTermHypotheses.lean:69` `every_character_of_theta_integrals_local_matching (P : UnitaryGroupThirdPlaceHypotheses) … : UpperTheory.EveryCharacter`，证明体转 `UpperTheory.Top.every_character_of_green_v_win (green_of_regular P.greenRegularCharacters) hV`。

证明体实际投影的字段（`:49-73`）：`litN`、`siegelWeilUnitaryConvergent`、`greenCuspidal`、`discreteSeriesCover`、`harishChandraModules`、`cuspRapidDecay`、`casselmanWallach`、`rayClassFieldSt`、`nLink`、`greenRegularCharacters`。
**`siegelEisensteinSimplePole` 不在其中**；全库对 `.siegelEisensteinSimplePole` 的投影只有 `HypothesisBundleConversions.lean:130,133`、`BhattScholzeCrystallineLattices.lean:84`，且那三处所属 bundle 的字段类型是真命题（见下）。

判定：**装载而不读取（carried, not consumed）**。它沿 root 的第一实参走到 `everyCharacter`，但没有任何定理从它推内容，所以不产生错误结论，只造成"这条输入已被满足"的外观。

**伴生事实（更要紧）**：同一数学事实存在**真编码**——`AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelEisensteinSimplePoleOfDoublingMethod.lean:14`
`def SiegelEisensteinSimplePole : Prop := ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL …, IsMaj V a → HasIwasawa …`，
并有 `EisPoleLEZeroOfLt.lean:46 simplePole_iff : Published.SiegelEisensteinSimplePole ↔ …`。
而主链所走的 `LocalTypeDictionary` / `ThirdPlaceSeries` 四个 bundle（`GeometricLemma.lean:73`、`BernsteinUnitaryProductIrreducibleBis.lean:198`、`…Ter.lean:64`、`ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:74`）把该位置换成 `UnusedSlot72`。

⟹ 定性改变：不是"档案缺这条数学事实"，而是**同一事实装了两套编码，主链用的是弱的那个（`True`）**。真版本仍在库里，且不与主链连通。

## 2.6 第二发现（比 2.5 更重）：极点在**结论内部**被挖掉，且被当作真前件消费

`UnusedSlot72` 作为裸前件的那条路（`twisted_siegel_weil_identity`）**不上 root 线**：
root 第三实参是 `theta_integrals_agree_and_local_matching_of_literature`（`EveryCharacterOfLiteratureOfVWin.lean:565`），
其体为 `PositivityTheory.ThKR.theoremK_head2 (eis_bl_of_literature O) (siegel_weil_std_of_literature O)`，不经 `twisted_siegel_weil_identity`。

但同一条"简单极点"事实，在 `doublingMethod` 上又挖了一次，这回挖在**目标命题的合取项里**：

**逐项对照**（两者形状完全相同，只差一个合取项）

- 真版 `GlobalTheory.Published.DoublingMethod`（`AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/EisRegularAtOfEisPoleLE.lean:36`），第 41–43 行：
  `(EisContinues … ∧ ∀ s₀, ∃ k, EisRegularAt … s₀ k) ∧ (V.rank < b → EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1) ∧ ∀ θ …, …`
- 空心版 `ResidueKilled.DM`（`Development/WeilBound/…/AnisotropicGlobalForms/DmOfHyp.lean:13`），第 18 行：
  `(EisContinues … ∧ ∀ s₀, ∃ k, EisRegularAt … s₀ k) ∧ **True** ∧ ∀ θ …, …`

即：`V.rank < b → EisPoleLE V … ((b − rank)/2) 1`（在 s=(b−rank)/2 处至多一阶极点）被替换成 `True`。

**包装关系**：`abbrev GlobalTheory.Published.DoublingMethodLocalZetaIntegrals : Prop := ResidueKilled.DM`
（`DiscreteSpectrumResidualClassification.lean:6`），下一行 `:7` 就是 `abbrev UnusedSlot72 : Prop := True`。
⟹ 这对空心件是**同一次手术的产物**，成对生成，正好与真版 `DoublingMethod` / `SiegelEisensteinSimplePole` 镜像。

**生产**：`dm_of_two : CuspRapidDecay → SiegelEisensteinContinuation → True → DM`（`DmOfHyp.lean:24`），
证明体 `intro hC hS _`——第三参数**直接丢弃**，极点位置写 `trivial`（`:27` `refine ⟨h1, trivial, …⟩`）；
文献包装 `doubling_method O := ResidueKilled.dm_of_two … trivial`（`EveryCharacterOfLiteratureOfVWin.lean:371-372`）。

**消费（这是关键，与 2.5 的"不读"不同）**：`doublingMethod` 是 `UnitaryGroupThirdPlaceHypotheses` 的字段（`:678`），
也被 `LocalTypeDictionary` 的 bundle 家族持有（`GeometricLemma.lean:33`），而它被**投影进真定理**：

- `ThetaTowerCompatibility.lean:15` `theta_tower_compatibility : WeilRepresentationUnitaryPair → CuspRapidDecay → DoublingMethodLocalZetaIntegrals → ∀ D …, …`
- 使用处：`HeckeFormAnisotropicOfRallisBottom.lean:30`、`RallisInnerProductBottomNormEq.lean:46`、`RealFunctionalsSeparateOfHypothesis.lean:27`、`FunctionalsSeparateFromRealInput.lean:19`、`OpenFirstParametersOfPublishedUE.lean:39`、`OntoXAndLamLowOfPublishedUE.lean:24`、`OpenOrbitOfUnramifiedExponents.lean:52`、`SurjectiveAndLowWeightOfUnramifiedExponents.lean:28`、`HeckeFormAnisoOfGlobalEuler.lean:135`、`HeckeFormAnisotropicRallis.lean:32`。

**判定升级**：2.5 的字段是"装载不读"；`doublingMethod` 是"**整块被读，而被掏空的那一项在任何使用点都无法提取**"。
（更正：上一版写成"读的是被掏空的那一项"是过头了——`True` 里提不出内容，所以那条极点事实是**彻底缺席**：既不被使用，也不被断言。）
凡经 `hP.doublingMethod` 下去的定理，其前件里"至多一阶极点"这一支恒为空槽，可用内容只剩 `EisContinues ∧ EisRegularAt ∧ BasicIdentity ∧ ZetaContinues`。

## 2.7 追到主轴：`doublingMethod` 确在 hub 路径上，`theta_tower_compatibility` 不在

方法：decl 级前向可达（`_rh14_reach.py`，索引 175,187 文件 / 1,055,043 声明，深度 4，展开 21,513 个 decl）。

从 hub `nonempty_hyps_definite_side_of_closed_bound`（`SiegelEisensteinSecondTermHypotheses.lean:44`）出发命中：

- 深度 2：`functionalsSeparate_of_howeUnram_of_siegelWeil` → `real_functionals_separate_of_hypothesis`（`LocalTypeDictionary/RealFunctionalsSeparateOfHypothesis.lean:15`）
- 该体 `:25-27` 把 `P.doublingMethod` 作为第 11 个实参传给 `GlobalTheory.T.twist_core_surjective`
- `TwistCoreSurjectiveOfLocalComponents.lean:15 / :32`：`… → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → … → CoreOnto`（第四段实参即 DM）
- `:18` 续传给 `twist_even_surjective_of_representatives`
- `TwistEvenSurjectiveOfRepresentatives.lean:13`：`… → DoublingMethodLocalZetaIntegrals → … → ∀ D, OntoAll D`
- `:15` `have hHecke := heckeForm_of_doubling' hWeil hCusp hSW hSWc hDoub hUnr D`
- `LocalTypeDictionary/HeckeFormOfDoubling.lean:16`：`… → DoublingMethodLocalZetaIntegrals → … → ∀ D, HeckeForm D`
- `:21` `hG : GlobalForm D := globalForm_of_siegel_weil p1 p2 p3 p4 p5 D`——**DM 的终落点**，受理者 `globalForm_of_siegel_weil`。

结论：
1. **DM 在 hub→root 这条主轴上，作为真前件被一路下传到底**（8 段实参链），不是"装载不读"。
2. 但可用的只有 `EisContinues ∧ EisRegularAt ∧ BasicIdentity ∧ ZetaContinues` 这一半；`V.rank < b → EisPoleLE … 1` 那一项是 `True`，**任何受理者都提不出来**。
3. `theta_tower_compatibility` **不在**这条路径上（深度 4 未达），它住在 `HeckeFormAnisotropicOfRallisBottom` / `RallisInnerProductBottomNormEq` 这一支。

对审计的含义：这条链**结论为真、内容为弱**——借它不会引入假命题；但它不携带"Siegel 艾森斯坦简单极点"这条数学事实（真版 `DoublingMethod` / `doublingMethod_of_three` 存在且完好，只是不在链上）。所以它不能作为我们论证的支点。

## 3. 顺带查实：`twisted_siegel_weil_identity` 的结论是"前件打包"

`TwistedSiegelWeilIdentityOfFormula.lean:25` 结论 `GlobalTheory.PrimIn.PublishedThetaConditionTheorems`，
证明体是 `⟨q1, q2, …, q7, sw, doubling_zeta_of_eisenstein_facts q2 e1 e2, q10, q11, q12, weilRepresentationUnitaryPair, q14⟩`。
第 9 项由 `q2 : CuspRapidDecay`、`e1 : SiegelEisensteinContinuation` 和 **`e2 : UnusedSlot72`（其值为 `trivial`）** 组成。

即：这条"定理"本身不产出数学内容——它把一个 14 字段的假设清单打成结构，其中一个字段靠 `e2 = trivial` 免检。
**借它等于借一张假设清单，不是借定理。** 这是"取代 vs 帮助"的第二种形态（第一种是装饰壳，见 `_rh14_decor_scan_report.md`）。

## 4. 纪律落地

- **黑名单（不得作为数学内容引用）**：`UnusedSlot72`、`UnusedSlot55`、`NoCondition`、`One.M.TrivialCondition`、`TrivialRankCondition`、`trivialClassCondition`（Prop 版）。
  理由：值为 `True`，引用它的命题在逻辑上等价于不引用。
- **允许**：`trivialClassCondition` 作 `PtClass` 参数（真值函数，参与 `valSet` / `HeckeFrameInt` 的实算）。
- **一句话判据**：凡出现在前件链里的槽，先问"去掉它结论还成立吗"——成立即说明该槽不承载内容；不成立再看它是否为 `True`。

## 5. 与本项目的关系

`UnusedSlot72` 不涉及零点统计，不进入 `EveryCharacter` 的推导内核；它是**代数–自守侧**的内部空洞。
对我们的用处只有一条：**它给出"验收口径"的样板**——任何要借入 RH_14 的定理，先用同一判据过一遍前件链，凡命中真空槽者一律降级为"假设清单"。
