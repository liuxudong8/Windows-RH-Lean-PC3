# Alpöge–Claude RH/GRH Lean 归档审计报告

> 审计对象：`https://alpo.ge/lean.tar.gz.part01..14`（2026-11-20 发布）
> 落盘：`F:\F\BSD_GRH_RH\RH_14\`
> 审计时间：2026-11-21
> 对照工程：`C:\proj2`（OrderPreservingBijection / BSD / QRH / A5CharQ5，toolchain `v4.34.0-rc2`）

---

## 0. 落盘与解包事实

| 项 | 数值 |
|---|---|
| 分卷 | 14 个，前 13 个各 18,000,000 字节，末卷 5,275,554 字节 |
| 合并后 | 239,275,554 字节（`lean.tar.gz`） |
| tar 条目 | 175,191 行，其中 395 行为 bsdtar「empty or unreadable filename」错误 |
| 解出 `.lean` | **174,793** 个（与条目数一致，无缺失） |
| 顶层非源码文件 | `lakefile.toml`、`lean-toolchain`、`lake-manifest.json` |
| 未解出条目 | 395（文件名不可读，非 `.lean`；不影响源码完整性） |
| 工程 pin | toolchain `leanprover/lean4:v4.33.1`，mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474` |
| 本地 mathlib | HEAD `f8d25bb…`（squash「init」），toolchain `v4.34.0-rc2` → **版本不匹配** |

`lakefile.toml` 结构：`srcDir = "src"`，11 个 lean_lib，`Main` 的 roots 为 `["Statements", "Main"]`；`autoImplicit = false`、`maxHeartbeats = 4000000`、`--tstack=400000`。

---

## ① 陈述对照（statement.lean vs 我们的 riemann_hypothesis）

### 他们的陈述层（全部代码只有 1216 字节）

`src/Statements.lean`（783 字节，仅 `import Mathlib`）—— 4 个定义：

```lean
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=  -- 开条带内的零点落在 1/2
def PrimitiveDirichletLZerosOnLine : Prop := -- 本原特征版本
```

`src/Main.lean`（433 字节，5 条定理，全部闭合）：

| 定理 | 类型 | 证明项 |
|---|---|---|
| `riemannHypothesis` | `RiemannHypothesis`（**Mathlib 原定义**，见 `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`） | `rhOfAll` |
| `riemannZeta_eq_zero_re` | `RiemannZetaZerosOnLine` | `rhOfAll` |
| `LFunction_ne_zero_of_half_lt_re` | `DirichletLNonvanishingRightOfHalf` | `allChi` |
| `LFunction_eq_zero_re` | `DirichletLZerosOnLine` | `claimAll.2.1` |
| `LFunction_eq_zero_re_of_isPrimitive` | `PrimitiveDirichletLZerosOnLine` | `critAll` |

### 我们的陈述（`OrderPreservingBijection/stage_4.lean:5912`）

```lean
theorem RHSpectralDuality.riemann_hypothesis
    (h_duality : ∀ (f : MollifiedTestFunction),
      spectralSum f.toTestFunction = nontrivialZeroSum f.toTestFunction)
    (h_win : UniformSupport)
    (f : MollifiedTestFunction) :
    ∀ (s : ℂ), riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2
```

闭包：`[propext, sorryAx, Classical.choice, Quot.sound]`（`_build_all_20261121.txt:4087`）。

### 并排差异（三层，全部对我们不利）

| 维度 | 他们 | 我们 | 后果 |
|---|---|---|---|
| **命题强度** | `RiemannHypothesis` 零参数闭合 | 带 `h_duality`、`h_win` 两个前提，且额外量化 `f` | 我们证的是「对偶 ⟹ RH」，不是 RH |
| **GRH 覆盖** | `EveryCharacter`：∀ N ∀ χ（含非本原）1/2<Re s ⟹ L≠0；另有 primitive 版 | Lean 里**没有** GRH 命题，只有 docstring 提「K-GRH」 | 我们的 GRH 是文档承诺，不是形式化目标 |
| **闭包** | 只有 3 条标准公理（外部独立编译确认） | 含 `sorryAx` | 我们的绿灯建立在 sorry 之上 |

**根因**：他们用「Λ 和的下界判据」直接产出 RH；我们把 Weil 显式公式的**等式本身**（`h_duality`）当输入，于是永远在 RH 之前停住。

---

## ② `#print axioms` 等价审计（静态全量扫描）

### 静态证据（174,793 文件全扫）

| 模式 | 命中 | 说明 |
|---|---|---|
| `axiom` 声明 | **0** | |
| `constant` 声明 | **0** | 这是最容易漏掉的假设入口，也为 0 |
| `opaque` 声明 | **0** | 无 opaque 洗白 |
| `unsafe` 声明 | **0** | |
| `sorry` | **0** | |
| `admit` | **0** | |
| `native_decide` | **0** | 无 `ofReduceBool` |
| `implemented_by` / `@[extern]` | **0** | 无编译期信任逃逸 |
| `partial def` | 2 | 局部辅助，非命题级 |
| `Lean.Elab.Tactic` 元编程 | 38 处 | 见下，全部是 `revertAll` 薄壳，仍过内核 |

**结论：没有藏 opaque，也没有命名 axiom 洗白。** 这条最关键的怀疑可以排除。

### 为什么没跑动态 `#print axioms`

他们的 pin 是 `v4.33.1` + mathlib `0df444a`，本地是 `v4.34.0-rc2` + `f8d25bb`。要动态跑 `#print axioms riemannHypothesis`，必须先按他们的 rev 拉取并预编译 mathlib（约 2–4 GB 下载 + 数小时），再编译 17.5 万文件。**本机当前不具备该条件**，未伪造结论。

外部独立证据可替代：Andrew Sutherland 已独立编译，报告「Lean proof has been compiled and independently re-checked by the Lean kernel with only the three standard axioms」。

### 依赖链拓扑（比 axiom 扫描更值得看）

```
Main.lean : riemannHypothesis
 └ rhOfAll : RiemannHypothesis            (Supplements/Kernels/MainTheorems.lean:9)
    └ Formalism.VW.rh_of_every allChi    (Formalism/GammaFactorNonvanishing/CritLine.lean:29)
       └ allChi : UpperTheory.EveryCharacter
          └ UpperTheory.FinalTheorems.everyCharacter
             └ everyCharacter_of_row (UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter)
                └ plugAll → plugWin → zeroFreeAll_of_topG
                   ├ GlobalTheory.GLq.Green
                   ├ UpperTheory.Top.VWin
                   └ Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)
```

`CritLine.lean:11` 的 `critLine` 是这一步的真正桥梁：用 `completedLFunction` 的函数方程 + `gammaFactor_ne_zero`，把「右半平面非零」转成「开条带零点在线上」。**这是纯 Mathlib 级技巧，可直接搬给我们。**

`Hyps` 定义在 `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/APerTw.lean:23`，是带 20+ 个 Prop 字段的 `structure`（`Duty`、`RowsB`、`TieTwRec`、`ClassNumberFormula₂`、`TheoremSSelected`、`CountAllPointsClass`…），抽样看字段不是 `True` 占位。

### 残余风险（公理层干净后，攻击面转移到「定义空转」）

1. `Nonempty (Hyps … DRS)` 是否由真实构造给出，而不是靠某个字段被定义成恒真。
2. `UpperTheory.GalStar.Row0b` 的实际内容。
3. `GlobalTheory.GLq.Green` / `UpperTheory.Top.VWin` 的定义（全量扫描未命中直接 `def Green`，可能在其它命名空间）。
4. 38 处 `run_tac Lean.Elab.Tactic.liftMetaTactic (… revertAll)` + `exact @lemma` 的薄壳模式，量大且同构——需确认不是同一引理的循环引用。

**判定**：公理层 `0 / 0 / 0 / 0 / 0`，比我们干净一个量级；但「无公理」≠「无空转」，上面 4 点未验完，不能替他们下最终结论。

---

## ③ 与他们「Weil 形式 + 惯性律」的逐条映射

> 先纠正上一轮我的表述：**11 月这份 drop 的主链不是秩–迹/惯性论证**，而是 `G χ x` 的 Λ 和判据（`Formalism/Statement.lean` 的 `RHofG`）。惯性律只出现在底层线性代数。8 月那篇 arXiv 2608.13637 才是 Weil 二次型 + Sylvester 论证。

### 映射表

| 他们的对象（路径） | 数学内容 | 我们的对应物 | 复用度 |
|---|---|---|---|
| `Formalism/Statement.lean:11-22` `LamF`, `S`, `gammaF`, `G` | `G χ x = Σ_{n≤x} Λ(n)(1+Re χ(n))(x/n−1) − x log x + (1+γ_χ)x` | 我们 `nontrivialZeroSum` / `spectralSum` 的素项侧 | **直接搬**（纯 Mathlib 定义，4 个 def） |
| `Formalism/Statement.lean:46` `RHofG` | `G ≤ −C x^{1/2+ε}` ⟹ RH ∧ 右半平面非零 | 我们的 `h_duality` + `h_win` 的实际内容 | **这正是我们缺的一环** |
| `Formalism/GammaFactorNonvanishing/CritLine.lean:11` `critLine` | 函数方程 + Γ 非零 ⟹ 条带零点在线上 | 我们 RH 主链从 test function 直接出发，缺此桥 | **直接搬**（GRH 侧关键补丁） |
| `…/CritLine.lean:6` `gammaFactor_ne_zero` | `0 < Re s ⟹ gammaFactor χ s ≠ 0` | 我们 Γ 因子层（未见等价引理） | **直接搬** |
| `…/TwistedOperators/HasSignatureFstUniqueSylvester.lean:116` `hasSignature_fst_unique` | `HasSignature J a b → HasSignature J a' b' → a = a'`（复矩阵，Sylvester 惯性唯一性） | 我们「正/负定子空间 ↔ 惯性指数」这一步 | **直接搬**（纯线性代数，零解析输入） |
| `Formalism/UG.HasSignature`（`Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean:181` 用到） | 签名谓词 (p,q) | 我们谱对偶的 signature 计数 | **直接搬** |
| `AdelicAnalysis/SumRhoEqTrace.lean:63` `sum_rho_eq_trace` | `Σ_w ρ_w c = trace_{ℚ→F} c` | 我们迹公式侧「Σρ = trace」标识 | 可搬写法（含 `InfinitePlace` 双射构造） |
| `AdelicAnalysis/RealQuadraticFormLemma…Statement.lean` | 二次型的 Fourier 系数积分公式 | 我们 Gram 矩阵 / Mellin 侧的积分恒等 | 可搬（需按其依赖 `CountData`/`QSetup` 重建） |
| `…/SymmetricInvertibleExistsPosdefCongruence`、`HermitianDiagonalizeOverReducedTensor` | 对称可逆 ⟹ 存在正定同余；Hermitian 对角化 | 我们 PWW 对偶的正定性步骤 | 可搬（同层线性代数） |
| `AdelicAnalysis/SiegelWeilOrbitalMeasure`、`WeilOperatorIntegralInvariance`、`WeilRepresentationQuadraticDatum` | Siegel–Weil 测度、Weil 算子的积分不变性 | 我们 `MollifiedTestFunction` / `UniformSupport` | 部分可搬（体量大，需按其 adelic 层重建） |
| 全库 `*Statement.lean` 薄壳模式 | 巨型显式类型 + `first \| exact @lemma` 再导出 | 我们 5912 行单文件 `stage_4.lean` | **工程范式，必须学** |

### 常数锚点：我们的 0.6725 就是他们的 0.6725

他们 8 月结果（arXiv 2608.13637，Alpöge–Furman）：「Montgomery–Taylor 窗下常数 0.6725 / 0.8362」，且已 Lean 4 形式化。我们 `BSD/BSD_summary.md §15` 的数值结论是「**0.6725 − O(10⁻⁵~10⁻³)**，缺口在 Levinson 常数不在余项」。**同一个常数、同一个窗口**——这意味着他们的 8 月形式化工程可以直接作为我们数值链的解析支撑，而不用自建。

---

## ④ 建议的执行序（按性价比）

1. **搬 `CritLine` 的桥**：把 `gammaFactor_ne_zero` + `completedLFunction` 函数方程那段搬进 `OrderPreservingBijection`，作为 K-GRH 的独立环。工作量小、纯 Mathlib。
2. **搬惯性唯一性**：引入 `HasSignature` + `hasSignature_fst_unique`，把 `spectralSum = nontrivialZeroSum` 的「正负定分解」写成有限维定理，**不需要任何解析数论公理**，可一次性消掉我们 axiom 白名单里一批（我们 BSD 侧 axiom 329 条）。
3. **学薄壳工程**：把 `stage_4.lean` 拆成 `Statement.lean`（只放命题）+ `Proof/*.lean`（每引理一文件）。我们 5912 行单文件是无法做 comparator 核验的。
4. **别急着引用他们的 RH**：comparator / paranoid 多内核未过，`Hyps` 空转风险未验完。等通过后，再把我们 GRH 侧的 axiom 降级为「引用外部已核定理」。
5. **可选**：按他们 pin（`v4.33.1` + mathlib `0df444a`）在 F 盘建第二个 mathlib 检出并预编译，之后才能在本机跑真正的 `#print axioms`。预计下载 2–4 GB、编译数小时。
