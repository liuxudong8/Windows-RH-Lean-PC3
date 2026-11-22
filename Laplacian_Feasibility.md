# 缺口① 处置：真 Laplacian 落地 + mathlib 可接性判断

日期：2026-11-22　　工程：`C:\proj2`　　结论文件配套：`OrderPreservingBijection/HyperbolicLaplacian.lean`

---

## 0. 三句话结论

1. **真算子已落地并验证**：`Δ_ℍ f = t² Δ_flat f − t ∂_t f`（ℍ³ 上半空间模型），5 条命题全部 kernel 级通过，axiom 集均为 `[propext, Classical.choice, Quot.sound]`。
2. **不能直接替换 `laplacian_M`**：它的签名是 `L2ManifoldM → L2ManifoldM` 的**全函数**，而 `L2ManifoldM` 的每个元素都携带 `measurable` 与 `sq_integrable` 证明；真 Laplacian 是无界算子，对任意 L² 函数填不出这两个证明。只能改定义域，或接受 junk 分支（后者会使 `laplacian_M_self_adjoint` 变假）。
3. **Rellich + 紧自伴谱定理在 mathlib 里接不上**，三层全缺，不是"补几条引理"的量级，是要从零建。

---

## 1. 算子本体

上半空间模型 ℍ³ = {(x, y, t) | t > 0}，度量 ds² = (dx² + dy² + dt²)/t²。

    √g = t⁻³,   gⁱʲ = t² δⁱʲ

    Δ_ℍ f = (1/√g) ∂ᵢ(√g gⁱʲ ∂ⱼ f) = t² Δ_flat f − t ∂_t f

`Δ_flat` 直接取 mathlib 的 `InnerProductSpace.Laplacian`（Hessian 的迹），第二项 −t∂_t 是度量带来的 Christoffel 修正。

坐标实现：`EuclideanSpace ℝ (Fin 3)`，坐标 2 即 t。**注意**：`ℂ × ℝ` 在 mathlib 里没有 `InnerProductSpace ℝ` 实例（`ProdL2` 的实例没覆盖它），所以必须绕到 `EuclideanSpace`。

---

## 2. kernel 级验证

| 命题 | 内容 | 结果 |
|---|---|---|
| `hyperbolicLaplacian_const` | `Δ_ℍ 常数 = 0`（0 特征空间 = 常数函数） | ✅ |
| `radialHLap_id` | `Δ_ℍ t = −t`（`s(s−2) = −1`，s = 1 支） | ✅ |
| `radialHLap_sq` | `Δ_ℍ t² = 0`（`s(s−2) = 0`，s = 2 支，即 t² 调和） | ✅ |
| `radialHLap_cube` | `Δ_ℍ t³ = 3t³`（`s(s−2) = 3`，s = 3 支） | ✅ |
| `spectral_bottom_three_dimensional` | `s = 1+iλ ⟹ s(2−s) = 1 + λ²` | ✅ |

axiom 实测（全部）：`[propext, Classical.choice, Quot.sound]`。无 `sorryAx`、无自定义 axiom。

这四条把归一化钉死了：`Δ_ℍ t^s = s(s−2) t^s`，故 `−Δ_ℍ` 在 `t^{1+iλ}` 上的特征值是 `1 + λ² ≥ 1`。

---

## 3. mathlib 现状核对（三层缺口）

| 需要的东西 | mathlib 有 | 缺什么 |
|---|---|---|
| 黎曼流形上的 Laplace–Beltrami | `Analysis/InnerProductSpace/Laplacian.lean`：`class Laplacian (E → F) (E → F)`、`instLaplacian`、`laplacianWithin`、`Δ` 记号。Δ = 二阶导张量的迹，**只在欧氏（flat）空间** | 全库 `Beltrami` 命中 0；无黎曼度量上的 Δ，无流形上的 Δ；`ℂ × ℝ` 的 `InnerProductSpace` 实例也没有 |
| Rellich–Kondrachov（H¹ ↪↪ L² 紧嵌入） | `Analysis/Distribution/Sobolev.lean`：`besselPotential`、`MemSobolev s p`（ℝⁿ 上、傅里叶/分布口径）；`Analysis/FunctionalSpaces/SobolevInequality.lean`：单个 Sobolev 不等式 | 全库 `Rellich` / `Kondrachov` 命中 0；无流形 H¹(M)、无紧嵌入、无椭圆正则性 |
| 无穷维紧自伴算子谱定理 | `Analysis/InnerProductSpace/Spectrum.lean` 是**有限维**谱定理（`Fin n`、`Module.finrank = n`、`eigenvectorBasis`、`diagonalization`）；`Analysis/Normed/Operator/Compact/FredholmAlternative.lean` 有 `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`、`hasEigenvalue_iff_mem_spectrum`（Fredholm 二择一） | 缺"紧自伴 ⟹ 特征向量构成 ONB + 特征值实 + λₙ → 0 + 可数枚举"；缺 λ₁ > 0 与无界性 |

三件加起来意味着：即便今天把算子换成真的，`laplacian_has_discrete_spectrum` 仍然证不出来——它需要 Rellich、紧自伴谱定理、以及 ℍ³/Γ 上的 Stokes 分部积分（自伴性）三样东西，mathlib 三样都没有。

---

## 4. 缺口①的性质变化（这一步的真实收益）

改之前：`laplacian_M := fun _ => Classical.arbitrary _`，`laplacian_has_discrete_spectrum` 是对这个空转占位的 `admit` —— 严格讲它连"真命题"都不是，是模型声明。

改之后（若采纳方案 A1）：`laplacian_M` 是真 Laplace–Beltrami，`laplacian_has_discrete_spectrum` 变成"对真算子、真几何条件的标准谱定理，因 mathlib 缺三件基础件而挂账"。依然是外部输入，但从"空洞"变成"可被未来兑现的条件"。

---

## 5. 副产品：1/4 是二维数字，三维的谱底是 1

`stage_4.lean` docstring 把 `1/4 ≤ s n` 标成"为下游 PointSetSeparable 服务的额外假设"，并引 Buser 1977 与算术曲面的 bass notes 讨论——那是 **ℍ²（二维）** 的数字。

ℍ³：`s = 1 + iλ` ⟹ `−Δ_ℍ` 特征值 `1 + λ² ≥ 1`；连续谱底也是 1（`((n−1)/2)²`，n = 3）。

所以对紧商 ℍ³/Γ，「1/4 ≤ s n」自动成立，不是风险点。这条 docstring 应该改。

---

## 6. 三条路线

- **A1（推荐）**：把 `laplacian_M` 的定义域改成光滑子空间（`SmoothL2ManifoldM := {f : L2ManifoldM // ContDiff … ∧ Δf ∈ L²}`），内部接 `hyperbolicLaplacian`。代价：`stage_4` + `HeatKernel` 共约 25 处引用要补光滑性；收益：占位变真算子，无 junk，缺口①表述精确。
- **A2（不推荐）**：签名不动，`laplacian_M` 写成 `if 光滑 then 真算子 else 0`。junk 分支会让 `laplacian_M_self_adjoint` 对非光滑输入为假，必须同时把该定理量化限制到光滑域——绕一圈回到 A1，还多一个 junk 概念。
- **A3（最小）**：只改 docstring，标注"占位，真算子见 `HyperbolicLaplacian.lean`"。零成本、零收益，仅防误读。

要实现真正的谱定理，需要独立支线：流形 Rellich（紧 Sobolev 嵌入）+ 可数 Hilbert 空间上的紧自伴 ONB 定理 + 流形 Stokes。规模远大于当前会话。

---

## 7. A1 已落地（2026-11-22）

新建 `OrderPreservingBijection/LaplacianBeltrami.lean`，内容：

| 声明 | 内容 |
|---|---|
| `halfSpaceSet` | `{p : ℂ × ℝ | 0 < p.2}` |
| `hypLift f` | 子类型上的函数提升到母空间（区域外取 0） |
| `eX / eY / eT` | `(1,0) / (I,0) / (0,1)`，ℝ 上正交归一 |
| `flatLapWithin f p` | `Σ_k iteratedFDerivWithin ℝ 2 f s p ![e_k, e_k]`（坐标迹） |
| `hyperbolicLapOn f p` | `t²·flatLap − t·fderivWithin f s p eT` |
| `SmoothL2ManifoldM` | 四字段：`toL2`、`contDiffOn`、`lap_measurable`、`lap_sq_integrable` |
| `laplacian_M` | `fun f => ⟨fun p => hyperbolicLapOn (hypLift f.toL2.toFun) p.val, …, …⟩` |
| `SmoothL2ManifoldM.ext` | 三项义务都是 Prop ⟹ `toL2` 相等即结构元相等 |
| `smoothZero`、`laplacian_M_apply` | 零元与逐点展开引理 |

改动的下游（**必要代价，不是顺手改**）：

- `HeatKernel.lean`：删掉占位 `laplacian_M`；新增 `heatOperatorSmooth`（`toL2 := heatOperator t f`，三个义务 sorry）与 `heatKernel_commutes_laplacian` 的量词改 `SmoothL2ManifoldM`。
- `stage_4.lean`：`laplacian_has_discrete_spectrum` 的自伴部分与特征向量量词改 `SmoothL2ManifoldM`；`specDiscM_is_eigenvalue` 返回光滑域元；`laplacian_M_self_adjoint` 量词改光滑域；新增 `shimuraLiftSmooth`（三个义务 sorry）与 `threeManifoldEigenfunctionSmooth`；`threeManifoldEigenfunction` 保留 `L2ManifoldM` 类型（= 光滑元的 `toL2`），使 `jl_l_parameter_preserving` 的 calc 链零改动成立；`jl_l_parameter_preserving` 内加 `h1s : shimuraLiftSmooth … = threeManifoldEigenfunctionSmooth n`（由 `ext` 从 L² 等式抬升）。

编译与实测：

- `lake build OrderPreservingBijection`：**3855 jobs 全部通过**（stage_4 单编 3852 jobs / 37 s）。
- `#print axioms`：`laplacian_M`、`SmoothL2ManifoldM.ext` 均为 `[propext, Classical.choice, Quot.sound]`（无 `sorryAx`）。
- 下游 `laplacian_M_self_adjoint` / `specDiscM_is_eigenvalue` / `threeManifold_eigenvalue_equation` / `shimuraLift_commutes_laplacian` / `heatKernel_commutes_laplacian` 仍是 `[…, sorryAx, …]` —— 因为 `laplacian_has_discrete_spectrum` 还是 `admit`。
- `Classical.arbitrary` 只剩 `laplacian_X`（二维，未做 A1；骨架相同，可直接复用本模块）。

**结论（必须说清）**：A1 的收益是「算子不再有 junk 值」，**不是**「少一个 sorry」。sorry 数不变。

---

## 8. A1 暴露的口径矛盾（比 Rellich 更根本）

`ManifoldM := UpperHalfSpace3 = {p : ℂ × ℝ // 0 < p.2}`，是**完整上半空间**，不是紧商 `ℍ³/Γ`。

由 `s(2−s) = 1 + λ²`：Δ_ℍ 的本征函数形如 `t^{1+iλ}·e^{i⟨k,z⟩}`。取 `s = 1 + iλ` 时 `|t^s|² = t²`，而体积元是 `dx dy dt / t³`，故

∫ |t^{1+iλ}|² dt/t³ = ∫ t²/t³ dt = ∫ dt/t  → 发散。

即：**在 L²(ℍ³) 上 Δ_ℍ 的点谱为空**（谱是连续谱 `[1,∞)`）。于是 `laplacian_has_discrete_spectrum` 里那条

`∀ n, ∃ ψ : L², ψ ≠ 0 ∧ Δ ψ = s n · ψ`

**在字面类型上是假命题**。它只在 `M = ℍ³/Γ`（Γ 余紧、无抛物元）时成立——而商根本没被形式化：`ManifoldM` 就是覆盖空间本身。

旧版 `laplacian_M := fun _ => arbitrary` 把这个矛盾盖住了（任何陈述对空转占位都「无所谓真假」）。A1 换成真算子后，矛盾变成可见的。

三条出路：

- **S0-a（推荐，成本最低）**：把该 axiom 改成条件句 —— 引入 `IsCocompactQuotient (Γ)` 谓词，陈述为 `IsCocompactQuotient Γ → 离散谱`，并注明当前 `ManifoldM` 是覆盖空间、谱结论属于商。仍是 `admit`，但字面为真、口径正确。
- **S0-b**：把 `ManifoldM` 换成真商类型 `Quotient (Γ-action)`。重活：`L2ManifoldM`、`hyperbolicMeasure3`、全部 25 处引用与 `shimuraLift` 全要重做。
- **S0-c**：维持现状，但在 docstring 明写「机制 A 假设下的建模声明；在完整 ℍ³ 上字面为假」。等于承认它是模型声明而非命题。

mathlib 侧的缺口（2026-11-22 复测，`C:\proj\mathlib4-master`，HEAD `f8d25bb`）：

| 关键件 | 命中数 |
|---|---|
| `Rellich` / `Kondrachov` / `CompactEmbedding` | 0 / 0 / 0 |
| 多维分部积分 `∫ f·∇g = −∫ ∇f·g` 型 | 0（只有 1 维 `integral_deriv_eq_sub`） |
| `IsSelfAdjoint`（递归全库） | **73**（两处定义：`Algebra/Star/SelfAdjoint.lean:50` 的 `star x = x`（代数/C*-代数口径，即有界元素）；`LinearAlgebra/SesquilinearForm/Basic.lean:484` 的 `LinearMap.IsSelfAdjoint B f := IsAdjointPair B B f f`（有限维双线性形式口径） |
| `EssentiallySelfAdjoint` / `UnboundedOperator` / `ClosedOperator` / `BorelFunctionalCalculus` | 0 / 0 / 0 / 0 |
| `SpectralTheorem` | 0 |

> **更正（2026-11-22，重要）**：本表初版是用浅层 glob `Mathlib\**\*.lean` 统计的，`**` 在 PowerShell 的 `-Path` 里只匹配一层，所以 `IsSelfAdjoint` 一行被误报成 0，我据此写了「mathlib 连自伴概念都没有」。用递归全扫（8407 个 .lean 文件）重查后更正为上表。
>
> 事实是：mathlib **有**自伴概念，但只到两个"有限/有界"层面——星代数元素（C*-代数元，有界）与有限维模上的双线性形式伴随。**无界算子**（我们的 Δ_ℍ 就是）需要的 essential self-adjointness、闭扩张、函数演算，四样命中全 0。所以结论方向不变（我们这条链仍然接不上），但理由必须改：不是"缺概念"，而是"概念只覆盖有界/有限情形，无界算子层是空白"。

所以「自伴性」这一环：mathlib 有代数/有界层面的概念（73 处），但无界算子的 essential self-adjointness 为 0。Rellich 依然接不上，四缺是：算子（已有）→ 无界自伴（缺 essential self-adjointness + 缺分部积分）→ 紧预解式（缺 Rellich）→ 谱定理（缺无穷维版本；C*-代数谱只覆盖有界元）。

---

## 9. S0-a 已落地（2026-11-22）

### 9.1 结构

`stage_4.lean` 在 `laplacian_X` 之后新增：

```lean
opaque CocompactQuotientHypothesis : Prop          -- 几何债的唯一命名点
theorem cocompactQuotientHypothesis : CocompactQuotientHypothesis := by sorry
```

并把原先「自伴性 ∧ 离散谱」的合并公理**拆成两条**：

| 声明 | 内容 | 是否带几何前提 |
|---|---|---|
| `laplacian_M_self_adjoint_bilinear` | `⟨Δf,g⟩ = ⟨f,Δg⟩`，`f,g : SmoothL2ManifoldM` | **不带**（分部积分与 Γ 无关） |
| `laplacian_has_discrete_spectrum (hQ : CocompactQuotientHypothesis)` | `∃ s, 0<s 0 ∧ (∀n, 1/4≤s n) ∧ 严格增 ∧ 无界 ∧ 每个 s n 有光滑特征向量` | 带 `hQ` |
| `laplacian_X_self_adjoint_bilinear` | 二维自伴性 | **不带** |
| `maass_laplacian_has_discrete_spectrum (hQ : …)` | 二维离散谱 | 带 `hQ` |
| `laplacian_M_self_adjoint` / `laplacian_X_self_adjoint` | 对外门面，转发到 `_bilinear` | 不带 |

`specDiscM` / `laplacian_spectral_gap` / `specDiscM_properties` / `specDiscM_is_eigenvalue` / `maassSpecParam` 系列内部统一改写为

```lean
Classical.choose (laplacian_has_discrete_spectrum cocompactQuotientHypothesis)
```

（级联 `and` 的投影路径因此整体少一层 `.2`，逐处校正过）。

### 9.2 实测

- `lake build OrderPreservingBijection`：**3855 jobs 全部通过**。
- `#print axioms`：
  - `laplacian_M_self_adjoint_bilinear`：`[propext, sorryAx, Classical.choice, Quot.sound]`，**不含几何债**。
  - `laplacian_has_discrete_spectrum`、`specDiscM`、`maassSpecParam`、`riemann_hypothesis`：同上形态。
  - `cocompactQuotientHypothesis`：`[sorryAx]`。

### 9.3 一个必须记住的技术事实（否则以后会误判）

`#print axioms` **不会**列出 `opaque CocompactQuotientHypothesis` 这个名字——它的证体是 `sorry`，`sorryAx` 已经把整条债吸收。也就是说：

- 这次改动的审计可见性落在**类型签名**（`hQ` 是必须填的显式参数），**不在 axiom 集**。
- 好处：任何想直接引用离散谱的人，类型上必须显式写 `cocompactQuotientHypothesis`，绕不过去。
- 剩下的漏洞：`specDiscM := Classical.choose (… cocompactQuotientHypothesis)` 把债**吸收进了定义**，下游用 `specDiscM`（几十处）时签名不再出现几何债，只按常规定理继承。要彻底堵住，得让 `specDiscM` 也带 `(hQ)` 参数——级联面太大（下游全部推导链都要补参数），当前不做。

### 9.4 现在的诚实口径

- `laplacian_has_discrete_spectrum` 是**条件句**：给定紧商前提，谱离散。字面为真（不再断言覆盖空间 ℍ³ 上有 L² 特征向量），内容仍挂 `sorry`（Rellich + 谱定理未形式化）。
- 覆盖空间 vs 商的矛盾不再被隐藏：`hQ` 出现在签名里，`CocompactQuotientHypothesis` 的 docstring 写明「`∫ t²/t³ dt = ∫ dt/t` 发散，故覆盖空间上字面为假」。
- 二维已同型处理（口径统一）；但 `laplacian_X` 本身仍是 `Classical.arbitrary` 占位，A1 的二维版（`LaplacianBeltramiX.lean`）尚未做——骨架可直接照抄三维，代价是 ℍ² 版的 `UpperHalfPlane`/`hyperbolicMeasure2` 坐标公式 `y²(f_xx+f_yy)`。

---

## 10. 二维算子的 A1 已落地（2026-11-22）

新建 `OrderPreservingBijection/LaplacianBeltramiX.lean`，与三维版同构，差别只在几何因子：

| 声明 | 内容 |
|---|---|
| `upperHalfPlaneSet` | `{z : ℂ | 0 < z.im}` |
| `planeLift f` | 子类型上的函数提升到 `ℂ`（区域外 0） |
| `exC / eyC` | `1` / `I`，ℝ 上正交归一 |
| `flatLapPlane f z` | `f_xx + f_yy`（两个 `iteratedFDerivWithin` 迹相加） |
| `hyperbolicLapPlane f z` | `y² · flatLapPlane f z`（**无一阶项**，因为 `√g = 1/y²`） |
| `SmoothL2ManifoldX` | 四字段：`toL2`、`contDiffOn`、`lap_measurable`、`lap_sq_integrable` |
| `laplacian_X` | `fun f => ⟨fun z => hyperbolicLapPlane (planeLift f.toL2.toFun) z.val, …⟩` |
| `SmoothL2ManifoldX.ext`、`smoothZeroX`、`laplacian_X_apply` | 外延/零元/逐点展开 |
| `hyperbolicLapPlane_const` | **真定理**：`Δ_ℍ (常数) = 0`（用 `iteratedFDerivWithin_const_of_ne`，证明干净） |
| `casimir_two_dimensional` | **真定理**：`s = 1/2+it ⟹ s(1−s) = 1/4 + t²`，这是「特征值 = 1/4+t_n²」的算术来源 |

`stage_4` 侧改动（与三维同型）：

- 删除占位 `laplacian_X`，改 `import LaplacianBeltramiX`。
- `maass_laplacian_has_discrete_spectrum (hQ)`：特征向量量词改 `SmoothL2ManifoldX`。
- `laplacian_X_self_adjoint_bilinear (f g : SmoothL2ManifoldX)`：不带 `hQ`。
- `maassSpecParam_is_eigenvalue` 返回光滑域元；新增 `maassEigenfunctionSmooth`；`maassEigenfunction` 保留 `L2ManifoldX`（= 光滑元的 `toL2`）。
- `maass_eigenvalue_equation`：`Δ_X (光滑版) = (1/4+t²) • φ_k`。
- `shimuraLift_standard_properties` (2) 与 `shimuraLift_commutes_laplacian` 量词改到 `SmoothL2ManifoldX`。
- `jl_l_parameter_preserving`：把 `laplacian_X (maassEigenfunction k)` 逐处换成 `laplacian_X (maassEigenfunctionSmooth k)`；calc 主体结构不变。

实测：

- `lake build OrderPreservingBijection`：**3856 jobs 全部通过**。
- `#print axioms`：`laplacian_X`、`SmoothL2ManifoldX.ext`、`hyperbolicLapPlane_const`、`casimir_two_dimensional` 全为 `[propext, Classical.choice, Quot.sound]`；`laplacian_X_self_adjoint_bilinear`、`maassSpecParam`、`maass_eigenvalue_equation` 仍含 `sorryAx`（离散谱与自伴性本身未证）。
- `Classical.arbitrary` 已从两维 Laplacian 中全部清除（全库只剩注释里的历史说明）。

至此两维算子都已是公式算出的真算子，无 junk 分支；剩下的缺口只有两类：**数学缺口**（无界自伴 + Rellich + 无穷维谱定理，mathlib 全空白）与**几何债**（`CocompactQuotientHypothesis`，已显式化在签名里）。
