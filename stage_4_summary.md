# Stage 4 总结 — RH/K-GRH 谱对偶论证框架

| 项目 | 值 |
|------|-----|
| 生成时间 | 2026-11-22（含 11/21–11/22 归档审计、惯性律搬运、A 矩阵显式化三组工作） |
| Lean 版本 | v4.34.0-rc2 |
| mathlib | `C:\proj\mathlib4-master`，HEAD `f8d25bb`（8407 个 .lean，已编译 olean 6952 个） |
| 项目路径 | `C:\proj2`（库名 `OrderPreservingBijection`，另有 `BSD`/`QRH`/`A5CharQ5` 三个 lean_lib） |
| 构建 | 单文件口径 `lake env lean <file> -o <olean>`；`stage_4.lean` 单编 2600–2700 jobs 通过（0 error）；`StatementAlign.lean` 回编 0 error |
| 归档对照侧 | `F:\F\BSD_GRH_RH\RH_14`（174,793 个 .lean，14 分卷 239,275,554 B） |

---

## 项目状态总览（2026-11-22 实测）

| 项目 | 数值 |
|------|------|
| `OrderPreservingBijection\` 下 .lean 文件 | 115（含 ~22 个 `test_*.lean` 探针，非交付） |
| `sorry`/`admit` 文本命中（活跃文件，含注释/docstring） | 148 |
| 其中 `stage_4.lean` | 52 命中（文本级；语句级为 38，差额在 docstring 与审计说明里） |
| `SylvesterInertia.lean` / `EllipticClasses.lean` 命中 | 2 / 2，**全在 docstring 里，定理体无 sorry** |
| 活跃文件自定义 `axiom` | **0**（仅两个 test 文件仍留 `axiom intervalIndicator_mellinTransform`） |
| `opaque` 声明（活跃文件） | **7**（`stage_4.lean` 5 条：`CocompactQuotientHypothesis`/`scatteringMatrixLogDerivative`/`shimuraKernel`/`jlSpectrumMap`/`transferOperator`；另有 `MollifiedFunction.ellipticWeight`、`HeatKernelConvolution.sphericalPoint`） |
| `#print axioms riemann_hypothesis` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| **主链自定义 axiom** | **0** |
| 归档侧静态审计 | `axiom 0 / constant 0 / opaque 0 / unsafe 0 / sorry 0 / admit 0 / native_decide 0` |

---

## 项目目标与数学框架【目标状态 2026-09-30 拍板，未变】

**当前形式化目标：K-GRH（Q(√5) 局部广义黎曼假设）**——ζ_K(s) = ζ(s)L(χ₅,s) 的全部非平凡零点 Re(ρ)=1/2，由谱对偶桥（Arthur 迹 + 保序双射 + JL 酉等价 + 显式公式）推出。

**Riemann ζ 的 RH 为长期目标**：需在文章层面补"ζ_K 零点侧 → ζ 零点侧"的桥（K-GRH 不蕴涵 RH：ζ 零点 ⊂ ζ_K 零点，反向推不出）。三篇源文献（数值匹配2 / 保序双射定理6 / 谱对偶论证9）的代数设定均为 K=Q(√5)（PSL₂(𝒪_K)），**不含 F=Q 设定**；第三篇明确放弃"Z_M(s)=ζ(s) 全域解析恒等"（类域论代数障碍 + 零点位置障碍 + k≥1 因子，数学上不可证明）。

```
Arthur 迹公式（紧支加权：谱侧 Σf(λ) = 几何侧 ΣW(γ)f(ℓ(γ)) + 椭圆 + Cont）
    ↓  保序双射 Φ:𝒢↔I_prim（第二篇，ℓ=log Nm，类数 h_K=1）
Jacquet-Langlands 酉等价（分裂素 w_p=1/2 局部酉投影归一，非人为抵消）
    ↓
K 素理想加权求和 ↔ ζ_K 显式公式（A2 修正后成立；非 ζ 显式公式）
    ↓  谱参数实值（自伴算子谱定理 + JL 酉等价，Dolgopyat 仅兜底）
λ = 1/4 + t², t∈ℝ ⟹ ρ = 1/2 + it ⟹ Re(ρ) = 1/2
    ↓
K-GRH（当前目标）→（待补桥）→ RH（长期目标）
```

---

## 已完成的主体工作

### 1. 基础设施层

| 模块 | 内容 |
|------|------|
| `BasicInfrastructure.lean` | TestFunction 类型（光滑紧支函数）、基本运算 |
| `MellinInfrastructure.lean` | Mellin 变换 `melinTransform f s` |
| `ManifoldInfrastructure.lean` | ℍ³/ℍ² 流形、`L2Function`、`gammaAction`、`gammaPeriodization` |
| `HyperbolicMeasure.lean` | `hyperbolicMeasure3/2`、`hyperbolicIntegral3` |
| `HeatKernel.lean` / `HeatKernelSemigroup.lean` / `HeatKernelConvolution.lean` | 热核、半群、卷积 |
| `MollifiedFunction.lean` | 磨光测试函数（`opaque ellipticWeight` 仍是未解释常数） |
| `EllipticClasses.lean`（11/21 新增） | 椭圆共轭类矩阵层：`GoldenMatrix`/`IsEllipticMatrix`/`ellipticClassLengths` + 有限性定理，替掉原 `opaque` + `by sorry` |
| `HyperbolicLaplacian.lean` | `hyperbolicLaplacian`、谱底 `1`（三维）/ `1/4`（二维） |
| `LaplacianBeltrami.lean`（11/21 新增） | 三维真 Laplace–Beltrami（`eX,eY,eT` 正交标架 + `(z.im)²(f_xx+f_yy)`），替换 `Classical.arbitrary` 占位 |
| `LaplacianBeltramiX.lean`（11/21 新增） | 二维版本 + `casimir_two_dimensional` |

### 2. 惯性律层（11/21 新增，从归档侧照抄）

`SylvesterInertia.lean`：356 行 / 30 条声明 / olean 1.06 MB。namespace `OrderPreservingBijection.SylvesterInertia`，10 个窄 import。

| 定理 | 内容 |
|------|------|
| `hasSignature_fst_unique` | 签名正部唯一（归档 `HasSignatureFstUniqueSylvester.lean` 101 行原样） |
| `sylvester_le` | 使 `Q ≤ 0` 的单射子空间维数 ≤ q |
| `hasSignature_of_frame` | `Qᴴ J Q = Jpq p q` ⟹ 签名 `(p,q)` |
| `hasSignature_fromBlocks` | `diag(A₁,A₂)` 签名可加（`(p+p', q+q')`） |
| 自建增补 | `card_eq_of_hasSignature`、`hasSignature_unique`（负部由总维数补）、`card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature`、`Jpq_eq_diagonal_elim_one_neg_one` |

九条主定理 axiom 全 `[propext, Classical.choice, Quot.sound]`，零警告。

**工程要点（必记）**：`import Mathlib` 会让 Lake 判定要重建整个 mathlib（1455 个模块从未编译），跑到 8761/8800 出现约 30 个 `failed to read .olean`——这些 olean 其实都在，是 32 个 lean 进程并发读取造成的间歇性假失败。唯一安全做法：把 import 收窄到具体模块，再 `lake env lean <file> -o <olean> -i <ilean>` 直接产 olean，绕开 Lake 全量判定。

### 3. 主定理层（`stage_4.lean`，6206 行）

`riemann_hypothesis (f : MollifiedTestFunction)` 为最终定理（陈述保留占位，目标 K-GRH）。关键中间定理：Perron 公式框架、Mellin 反演、零点加权可和性、成对局部化、对偶范数下界、统一支集、`mellin_transform_C2_rapid_decay`（真证）、`off_critical_line_contradiction` 反证主链。

11/21–11/22 新增两节（见后文 Q/R）：

- **A 矩阵的符号差接口**：`ADefiniteSignature` + 6 条 `aSignature_*` / `aNegativeDim_le`
- **Weil 二次型的 Gram 矩阵（显式）**：`weilGramMatrix` + 3 条 `weilGram_*`
- 尾部 `#print axioms` 审计清单从 13 条扩到 **16 条**

---

## 本轮工作（2026-09-28 ～ 09-30，历史）

### A. Axiom 批量降级（9/28，~28 个）
静默 `axiom X : T` → `lemma X : T := by sorry`，漏洞显性化；快照入 `c:\proj2\archive\`（49 个文件）。删除错误文件 `stage_4_m.lean`。

### B. 主链自定义 axiom 清零（9/28）
`nontrivialZero_im_ne_zero` 经 Dirichlet eta 桥接降级为 theorem。

### C. ZetaZeros 重构（9/28）
`zeroMultiplicity` opaque→def；`zeroMultiplicity_symmetry` → theorem（带假设）。

### D. mathlib 桥接（9/28）
`riemannZeta_conj`、`second_moment_gaussian_integral`、`cauchy_theorem_contour` → mathlib 现成定理。

### E. CompletedZeta.lean（9/28）
ξ(s) = (1/2)s(s-1)·completedRiemannZeta(s)；`xi_one_sub` 完整证明。

### F. `zeroMultiplicity_symmetry` 通关（9/29）
函数方程 + Γℝ 非零 + 因子非零 + 邻域内解析阶乘数链。

### G. η = (1-2^{1-s})·ζ 在 Re s>1（9/29）
踩坑：`((n+1:ℕ):ℂ)` cast 一致性、`HasSum.congr_fun`、偶部/奇部 `tsum_add`。

### H. ζ 在 (0,1) 实段为负（9/30，`riemannZeta_neg_on_Ioo`）
成对级数 `etaPaired` + 恒等式延拓到四片凸集并 `etaDomain`（避开 s=1）。`nontrivialZero_im_ne_zero` 彻底落地。

### I. ContourIntegral `:109` 围道内重构（9/30）
`:109` 改为 `contourIntegral = zetaZeroSide f − farZeroContribution f`；`:115` 真填；`:128` rw。

### J. ZetaZeros 重构（9/30）
`contourZeroFinset_finite`、`contourZeroFinset`、`farZeroContribution`、拆分版 `nontrivialZeroSum`、`nontrivialZeroSum_localization` 重写。

### K. Weil exact 重构（9/30）
保留 weylError 项；新增 `weil_explicit_formula_exact`（admit，核心对偶假设）、`weyl_far_error_pairing`（真定理）。

### L. 三篇源文献审计 + 目标下调（9/30，★ 定盘）
1. 代数设定三篇均为 K=Q(√5)，无 F=Q 依据。
2. 文章三处瑕疵：**A2 惯性素（最关键）**、A1 口径（紧致 vs 非紧）、A3 连续谱声明。
3. 目标下调：K-GRH（当前）→ RH（长期）。Lean 侧三处 docstring 标注目标状态。

---

## 本轮工作（2026-11-21 ～ 11-22）

### M. 归档 RH_14 下载与静态全扫

14 个分卷拉到 `F:\F\BSD_GRH_RH\RH_14`，合计 **239,275,554 B**，解出 **174,793 个 `.lean`**。源码根 `RH_14\lean\src`。

静态全扫结果（文本层）：`axiom 0 / constant 0 / opaque 0 / unsafe 0 / sorry 0 / admit 0 / native_decide 0`；仅 2 处 `partial def`、38 处 `Lean.Elab.Tactic` 函数外壳。**"没藏 opaque 洗白"在文本层已有答案。**

pin：toolchain `leanprover/lean4:v4.33.1`、mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474`、`lakefile.toml` 有 `moreLeanArgs=["--tstack=400000"]`、`maxHeartbeats=4000000`。归档侧共 **246 个 .lean 文件** 使用 `HasSignature`——惯性律是他们体系的底层公共件。

新闻侧结论（用户贴的两张自媒体截图）：Levent Alpöge 的声明真实存在，但属**作者自宣、未经数学界独立验证**；"25 万页文本 + 已 Lean 形式化"这一细节对应其公开的 Lean 归档。

### N. 定理层 `#print axioms` 不可达 → 陈述层单编替代

`#print axioms riemannHypothesis` 依赖闭包 175,133/175,187 模块、峰值内存 6.4–7.8 GB/进程，本机提交上限 39.7 GB ⟹ **不可达**。结论落 `Build_Feasibility.md`。

替代路径：只编 `Statements`（只依赖 Mathlib）→ 4 个 def 的 axiom 集全为 `[propext, Classical.choice, Quot.sound]`；`RiemannHypothesis` 与 `RiemannZetaZerosOnLine` 经 `rfl` 判等（**陈述层无弱化**）；产物 `stmtbuild\Statements.olean` 20,784 B。

### O. 惯性律四条搬运（→ `SylvesterInertia.lean`）

见"已完成的主体工作 §2"。三条要点：
1. 归档 `Formalism/SatakeDualWeyl/Statement.lean`（463 行，只 `import Mathlib`）里的 `cT`(:13)、`Jpq`(:104)、`HasSignature`(:483) 是全部依赖，原样照抄。
2. 归档只证正部；负部靠 `omega` 从总维数 `card n = p + q` 补出，得到本侧需要的 `hasSignature_unique`。
3. `hasSignature_fromBlocks` 的非平凡步骤是重排器 `σ = (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)`；**三块以上必须重造这种 `⊕` 换序器，不能递归套用**。

### P. `sorryAx` 源头追踪、真算子替换、S0-a 口径矛盾

1. 追 `sorryAx` 源头得 6 个具名源头。修 E 链（新建 `EllipticClasses.lean`）后 **6 → 5**。
2. `laplacian_M` 从 `Classical.arbitrary` 换成真 Laplace–Beltrami，立刻暴露口径矛盾：`ManifoldM` 是覆盖空间 ℍ³ 而非紧商 ℍ³/Γ，`t^{1+iλ}` 在 `dxdydt/t³` 下 `∫t²/t³ = ∫dt/t` 发散 ⟹ L²(ℍ³) 上点谱为空 ⟹ **原公理字面为假**。
3. 拍板 S0-a：`opaque CocompactQuotientHypothesis : Prop` + `theorem cocompactQuotientHypothesis := by sorry`，把"自伴 ∧ 离散谱"拆成两条。再建二维版 `LaplacianBeltramiX.lean`（`hyperbolicLapPlane f z = (z.im)²(f_xx+f_yy)`）+ 两条真定理。全库 3856 jobs 通过。
4. **收益口径（必须写清）**：A1 的收益是**去掉 junk，不是减少 sorry**，数量不变。`cocompactQuotientHypothesis` 的 axiom 集只显示 `[sorryAx]`——S0-a 的可审计性落在类型签名，不在 axiom 集。
5. **一处自我更正（勿再犯）**：早期断言"mathlib 连自伴概念都没有"是错的，根因是 `Select-String -Path "Mathlib\**\*.lean"` 里 `**` 只匹配一层。用 `Get-ChildItem -Recurse`（8407 个 .lean）重查：`IsSelfAdjoint` 73 命中；但 `EssentiallySelfAdjoint` / `UnboundedOperator` / `ClosedOperator` / `BorelFunctionalCalculus` 递归全库 **0 命中**，链仍接不上（理由改为"概念只到有界/有限层"）。

### Q. `stage_4.lean`：A 符号差接口 + Weil Gram 显式矩阵

**A 符号差接口**（`namespace RHSpectralDuality` 末尾新增一节）：

| 定理 | 内容 | axiom |
|---|---|---|
| `aSignature_wellDefined` | 签名唯一（`p = p' ∧ q = q'`） | `[propext, Classical.choice, Quot.sound]` |
| `aSignature_dim` | `card n = p + q` | 同上 |
| `aSignature_fromBlocks` | 分块可加 | 同上 |
| `aSignature_of_frame` | 显式合同变换即得签名 | 同上 |
| `aNegativeDim_le` | 负向子空间维数 `≤ q` | 同上 |
| `aSignature_fst_unique` | 正部唯一（归档原始形式） | 同上 |

**Weil Gram 显式矩阵**：`weilGramMatrix hz hp = Matrix.diagonal hz - hp`；三条定理 `weilGram_conjTranspose`（`Aᴴ = A`）、`weilGram_quadratic`（`star x ⬝ᵥ (A *ᵥ x) = Σ_j hz_j |x_j|² − star x ⬝ᵥ (hp *ᵥ x)`）、`weilGram_negativeDim_le`，axiom 全干净。

**口径（不得省略）**：本侧没有 `φ̂_j(ρ)` 的 Lean 表示，零点侧**只保留对角** `hz_j = Σ_ρ |φ̂_j(ρ)|²`，丢掉 `j ≠ k` 交叉项；素数侧保留满矩阵。写出的不是 Weil 二次型本身，而是它的**对角截断模型**。

**一处更正**：`weil_explicit_formula_trivial_terms_cancel` 与 `nontrivial_zero_sum_pair_separation` 的 axiom 输出被折行，此前推断"可能无 sorryAx"是错的；实测两条都含 `sorryAx`。

### R. `WeilGramConcrete.lean`：素数侧可算 + ‖φ̂‖² 解析上界

新模块 256 行，13 条定理零 error、零警告，olean 248,384 B。两个抽象入参都变成对象：

1. **素数侧**：`localGram p φ ψ = ∫₀¹ e^{-x log p} φ(x) \overline{ψ(x)} dx`；`weilPrimeGram N φ j k = Σ_{p ∈ Nat.primesBelow N} (log p)·localGram p (φ j) (φ k)`；厄米性点式 + 矩阵式都证（关键是把 `star` 穿过区间积分、并证明实值权 `p^{-x}` 对 `star` 不变）。
2. **零点侧上界**：`phiHat φ ρ = ∫₀¹ φ(x) e^{iρx} dx`，`‖φ̂(ρ)‖ ≤ e^{‖ρ‖}∫₀¹‖φ‖`，`‖φ̂‖² ≤ (e^{T})²(∫‖φ‖)²`（`‖ρ‖ ≤ T`）；`weilZeroDiag S φ j = Σ_{ρ∈S} ‖φ̂_j(ρ)‖²`，`hz_j ≤ card S·(e^{T})²(∫‖φ_j‖)²`。
3. **组装**：`weilGramConcrete S N φ = weilGramMatrix (weilZeroDiag S φ) (weilPrimeGram N φ)`；`Aᴴ = A`、二次型展开、`weilGramConcrete_negativeDim_le`（签名假设下 `card k ≤ q`）。
4. **硬边界（三条，别说过头）**：
   - 真 `⟨φ_j,φ_k⟩_p` 是 ℚ_p^* 上 Haar 积分；mathlib 有 `Padic` 但无 p 进 Haar 测度接口，故用 `p^{-x}`（乘法绝对值 `p^{-v}` 的阿基米德化写法）作局部权——**不是 Haar 测度本身**。
   - 素数侧是有限截断 `N`，零点侧是有限集 `S` + 只对角。
   - 素数枚举与 `log` 真可算，但局部内积是区间积分（经典非可计算对象），所以整条链是"定义显式、条目存在"，**不是 `#eval` 能跑出数值**。
   - 签名 `(p,q)` 仍是假设（`hSig`），本模块把"条目存在 + 厄米 + 界"做实，"知道 A 的签名"仍空。

---

## 剩余 `sorry`/`admit` 分布（2026-11-22 实测，文本命中，含注释）

| 文件 | 命中 | 说明 |
|------|------|------|
| `stage_4.lean` | 52 | 主链估计 + 核心对偶 admit（语句级 38） |
| `HeatKernel.lean` | 14 | 热核 HS 估计 |
| `ManifoldInfrastructure.lean` | 11 | 流形分析估计 |
| `MellinInfrastructure.lean` | 9 | Mellin 估计 |
| `HeatKernelConvolution.lean` | 8 | 卷积估计 |
| `Interpolation.lean` | 8 | 插值估计 |
| `BijectionPhi\Basic.lean` | 8 | 对偶映射分析 |
| `stage_3.lean` | 6 | Stage 3 桥接 |
| `ZetaZeros.lean` | 3 | `nontrivialZeroEnum_exists`（S 无限，用户保留）等 |
| `HeckeBridge.lean` | 3 | |
| `ContourIntegral.lean` | 1 | `:1699` 素 Dirichlet 差的 `CircleIntegrable`（`:115` 已真填） |
| `MollifiedFunction.lean` | 1 | 磨光函数 |
| `EllipticClasses.lean` / `SylvesterInertia.lean` | 2 / 2 | **全在 docstring，定理体无 sorry** |
| `test_*.lean` | ~22 | 探针（非交付） |

## 剩余 `opaque`（7 条，活跃文件）

| 位置 | 名称 |
|------|------|
| `stage_4.lean` | `CocompactQuotientHypothesis`（S0-a 几何前提条件句） |
| `stage_4.lean` | `scatteringMatrixLogDerivative`、`shimuraKernel`、`jlSpectrumMap`、`transferOperator` |
| `MollifiedFunction.lean` | `ellipticWeight`（kernel 干净但语义空，权重公式未形式化） |
| `HeatKernelConvolution.lean` | `sphericalPoint` |

自定义 `axiom`：活跃文件 **0**；仅 `test_interval_indicator.lean` / `test_det_factor.lean` 留有 `axiom intervalIndicator_mellinTransform`（探针，非交付）。

---

## 已知真缺口（mathlib `f8d25bb` 实测，递归全扫 8407 个 .lean）

1. **无界自伴算子链**：`EssentiallySelfAdjoint` 0、`UnboundedOperator` 0、`ClosedOperator` 0、`BorelFunctionalCalculus` 0；`IsSelfAdjoint` 有 73 命中但只到有界/有限层。
2. **紧预解式**：`Rellich` 0、`Kondrachov` 0、`CompactEmbedding` 0；谱定理 `SpectralTheorem` 0（只有 `hasEigenvalue_or_mem_resolventSet` 1 命中，`Compact/FredholmAlternative.lean`）。
3. **多维分部积分**：0 命中。
4. **p 进 Haar 测度**：有 `Padic`，无测度论接口（本侧用 `p^{-x}` 显式权替代）。
5. **一般留数定理**：mathlib 无留数理论（`ContourIntegral :109` 蓝图第一步依赖它）。
6. **S 无限（Weyl/Hardy）**：`nontrivialZeroEnum_exists` 保留 sorry（S 可数已证）。
7. **Dolgopyat 指数混合**：几何兜底（非主证明）。
8. **Arthur 迹公式 / JL 酉等价完整形式化**：表示论大工程，admit 级。
9. **A2 惯性素处理（文章层）**：决定 K-GRH 桥成立与否。

（已闭合：ζ 在 (0,1) 无实零点——H；`:115` 围道留数和——I；主链零自定义 axiom——B；E 链 sorry 源头——P。）

---

## 已验证做不通（勿重试）

- `lake build -j24` / `LAKE_JOBS`：该版 Lake 不认
- `lake exe cache get`：缺 git 且 github 不通
- `gitee.com/mirrors/mathlib4`：返回 `Unauthorized`；`mathlib.cache.azure.net`：全 FAIL
- 归档侧定理层 `#print axioms riemannHypothesis`：峰值内存超本机提交上限
- `lake build` 对 `import Mathlib` 文件：触发 mathlib 全量重建 + 约 30 个模块假读失败（改用 `lake env lean -o`）

---

## 下一步

1. **把 `WeilGramConcrete` 的三条产物接进主链审计清单**：目前 `stage_4.lean` 尾部 16 条 `#print axioms` 还没包含 `WeilGramConcrete` 的 13 条（跨文件，需另设审计入口）。
2. **A 的数值化**：`S` 换成临界线上由 `N(T)` 控制的零点计数集合（mathlib 无零点枚举，要另建计数层）；或用 `Nat.primesBelow 100` 做 `n = 2` 小规模素数侧矩阵，把"定义能跑"变成"矩阵能算"。
3. **`hz` 口径补论证**：零点侧对角线截断（丢 `j ≠ k` 交叉项）是否需要写一条不等式估计说明误差可控。
4. **K-GRH 落地**：零点基础设施从 Riemann ζ 换成 ζ_K（需 Dedekind zeta / L(χ₅) / K 素理想 von Mangoldt——mathlib 无）。
5. 逐步降级 `stage_4.lean` 的 38 个语句级假设；`laplacian_M`/`laplacian_X` 的无界自伴性仍 `admit`，等 mathlib 补链。

---

## S. 2026-11-23：与 Alpöge–Claude 论文（164 页，2026-11-21）对照后的口径修正

来源：`C:\proj2\Alpoge_Paper_Compare.md`（完整对照与证据）。

**S.1 路线修正（重要，必须覆盖旧说法）**
论文把证明链写成 `(M) + B + C ⇒ Estimate A ⇒ G(x) ≤ x^{1/2+ε}（在 [Y, Y^{3/2}]）⇒ RH`；公告的步骤 4、6（Weil 型正性 `W(f) ≥ 0`、由正性得无零点区）被论文明确记为 “an earlier form of our first step”，最终论证改用 Landau 型单边引理。**结论**：本摘要 M–R 里我们这条谱对偶链（Weil 显式公式、A 签名、双曲 Laplacian、Weil Gram）是 Weil/Lax–Phillips 正性路线，与这条最终证明**平行而不相交**；不得再表述为“与 Alpöge–Claude 对齐”。它的数学仍然成立，只是不是他们的数学。

**S.2 (M) 的边界是分层的**
论文自承 (M) `is not proved here`。但形式层里 (M) 的等式形式有对象：`AskMainBalance`（`Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:98`，内容 `ASK − MAIN = De`，即论文 Part II (5.3) 的精确恒等式），由 `colour_balance`（`…/ChainSlopeWindows/StronglyIrreducible.lean:695`）证，全库 0 sorry。故：**人类可读层缺 (M)，形式层不缺，但形式层未过评审、本机亦无法复核定理层**。三层可信度分开说。

**S.3 实测核对（本轮，替换旧数）**
- 14 分卷 joined 后 SHA-256 = `9631b4f0…f49c7fc`，与论文第 53 页所载**逐字节一致**；
- `.lean` 文件 **175,187**（此前报 174,793 是早期解包计数，差额 394；旧“全库扫描”覆盖面少 0.22%，本轮已在完整体上重跑）；
- 总行数 **17,374,215**，与“about 17 million lines”一致；
- 论文编号引用 [1]–[29] **29/29 在档**（[22] 为 `DataParams₂.lean`，U+2082）；全文 64 个不同 `X.lean` 引用 64/64 命中；行号抽查 `def VWin` 落 `ExistsPageN.lean:49`，与论文一致；
- 文本层声明总数 **1,066,087**（theorem 784,092 / def 212,819 / lemma 34,663 / abbrev 13,202 / structure 8,286 / instance 8,199 / example 4,662 / inductive 121 / class 43）；论文自报依赖闭包 **1,478,198**，高出 412,111（38.7%），系 kernel 生成声明（`match_`/`_proof_`/投影/recursor）不占源码行所致，**无 olean 不可复核**；
- 静态重扫（完整 175,187）：`axiom/constant/opaque/unsafe/sorry/admit/native_decide` 全 0，`partial def` 2（元编程）。

**S.4 新增模块（已编译，零警告）**
`OrderPreservingBijection/WeilGramSharp.lean`：上半平面 `0 ≤ Im ρ` 上相位模 `≤ 1`，把 `hz` 的解析界从 `card S · (exp T)² · (∫‖φ‖)²` 收紧为 `card S · (∫‖φ‖)²`。六条定理 axiom 全 `[propext, Classical.choice, Quot.sound]`（日志 `_wgs_out.txt`）。硬边界：只做上半平面，下半平面需共轭配对（未写）；对角截断与 `j ≠ k` 交叉项照旧缺。

**S.5 `ASK`/`MAIN` 与论文 (I.25)/(I.26) 同物**
`ASK = Σ_{惯性 p} 2 log p · [Σ_i max(a/p^i − w)₊] + log d · askD`，`MAIN = a(log a − 1 − γ + ℓ(chC) − ⟨log w⟩)`。这两条与论文的 `P`、`M` 是同一组对象，不是“相似”。

**S.6 下一步口径**
原“下一步”第 3 条（`hz` 口径补论证）改由此文 S.4 承接；新增优先级（照 `Alpoge_Paper_Compare.md` §6）：补完 `hz` 的下半平面与交叉项 → 引入预算式模板（照归档 `[6]` 的 `SizeWindows`/`GrowthBound` 形状）→ 素数侧换 `primVal`/`cosetMean` 型权 → 独立形化 Landau 单边引理（区间版）。
