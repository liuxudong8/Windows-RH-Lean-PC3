# Alpöge–Claude 论文 vs 我们的工作：对照、修正与可复用清单

> 对象：《The Alpöge–Claude proof of the Riemann hypothesis explained for the Riemann zeta function》，164 页，Working draft 2026-11-21，署名 “Claude Fable 5.2, Codex Astra 6.2, and Gemini Carbon at the behest of Michael O. Rubinstein”。
> 基准：`C:\proj2`（toolchain v4.34.0-rc2，mathlib `f8d25bb`），归档 `F:\F\BSD_GRH_RH\RH_14`。
> 本文所有数字都是本轮实测，不是引述；凡属定理的，标明其 Lean 名字；凡属数据的，标明它只是数据。

---

## 0. 一句话结论

论文把证明链写成 **(M) + B + C ⇒ Estimate A ⇒ G(x) ≤ x^{1/2+ε}（在 [Y, Y^{3/2}] 上）⇒ RH**，并自己声明 **(M) 不在论文里证**。这修正了我们此前的两点判断：

1. **路线错了**：这不是 Weil 正性/谱路线。公告的步骤 4、6（Weil 型正性、由正性得无零点区）被论文明确记为 “an earlier form of our first step”，最终论证改用 Landau 型单边引理。我们 `stage_4` 那条谱对偶链（Weil 显式公式、A 矩阵签名、双曲 Laplacian、Gram 矩阵）**不在**这条最终证明里。
2. **“没证”是分层**：人类可读层缺 (M)；形式层里 (M) 的等式形式 `AskMainBalance` 由 `colour_balance` 承担。所以“未证”指的是**写出来没写完**，不是 Lean 里空着——这与我们此前的静态审计（0 sorry / 0 axiom）是一致的，而不是矛盾。

---

## 1. 硬事实核对（全部本轮实测）

### 1.1 论文与我们的归档是同一个物体

| 项 | 论文说法 | 我们实测 | 判定 |
|---|---|---|---|
| 分卷数 | 14（`alpo.ge`） | 14 个 part，joined 后 239,275,554 B | 一致 |
| 整包 SHA-256 | `9631b4f0…f49c7fc` | `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` | **逐字节一致** |
| `.lean` 文件数 | 175,187 | 175,187（`os.walk`） | **一致** |
| 总行数 | “about 17 million lines” | 17,374,215 | 一致 |
| 编号引用文件 [1]–[29] | 给了 29 条路径 | **29/29 全部在**（[22] 是 `DataParams₂.lean`，文件名字符 U+2082，与论文括注一致） | 一致 |
| 全文 64 个不同 `X.lean` 引用 | — | 64/64 命中（同一个 U+2082 名字） | 一致 |

> 更正一处旧数：上一轮我报的是 174,793 个 `.lean`，那是早期解包计数（有 394 个因文件名/路径问题没算进去）。以 `os.walk` 重数为 175,187，与论文一致。旧报告里“全库扫描覆盖 174,793”这句话，覆盖面其实少 0.22%；本轮已在完整 175,187 上重跑。

### 1.2 静态审计（在完整 175,187 个文件上重跑）

| 模式 | 命中 |
|---|---|
| `axiom` / `constant` / `opaque` | 0 / 0 / 0 |
| `unsafe` | 0 |
| `sorry` / `admit` | 0 / 0 |
| `native_decide` | 0 |
| `partial def` | 2（`CutCptCopy.lean:41`、`OwnStruct.lean:18`，都是元编程） |

文本层声明总数（正则计数，只算行首声明头）：**1,066,087**
（theorem 784,092 / def 212,819 / lemma 34,663 / abbrev 13,202 / structure 8,286 / instance 8,199 / example 4,662 / inductive 121 / class 43）

论文说 `riemannHypothesis` 的依赖闭包含 **1,478,198 条声明**，比我们数出的源级声明多 **412,111（38.7%）**。这个差额不是矛盾，而是口径差：kernel 里还有 `match_N`、`_proof_N`、结构投影、recursor、instance 体等**不占源码行**的生成声明。我们没有 olean 级的闭包数据，所以这个数**我们核不了**——记为“论文自报，未复核”。

### 1.3 引用是否真的落在归档里（抽查 3 类）

| 检查 | 结果 |
|---|---|
| 19 个“声明名 ↔ 文件”配对（如 `each_unit_bound_statement` ↔ `LevelOfCongruence.lean`） | 19/19 在该文件内逐字出现（另有 5 个解析假阳性，是英文词被误抓） |
| 行号抽查：`def VWin : Prop` | 论文写 `ExistsPageN.lean:49`，实测**正是第 49 行** |
| 313 个 `(Lean: …)` 括注里的标识符 | 246 个逐字存在；其余多为散文词或断行截断；清洗后仅约 10 个未定位（多为带命名空间前缀的写法） |

结论：论文的 Lean 引用**不是编的**，而且带精确行号。这一点比上一轮的“新闻核实”强得多——上一轮只能证明“人和声明存在”，这一轮能证明“它引用的每一条都能在归档里落到行”。

---

## 2. 论文改变了我们什么（三条修正）

### 修正 1：路线不是谱对偶，是 Chebyshev–Stepanov 型“整除 ≤ 大小”

论文的五个步骤（§I.0）：

1. 零点 → 带 ramp 的素数统计 `G(x) = Σ_n Λ(n)(x/n−1)₊ − x log x + (1+γ)x`，且**只需单边**上界（Landau 型引理，含区间版）；
2. Chebyshev 法为什么卡住：阶乘的指数带 floor，`Σ Λ(r){n/r}` 量级与主项相同；
3. 换成“指数光滑”的可除对象：CM 椭圆曲线上函数的导数，在**惯性素数**处的指数是 `a(1/p + 1/p³ + ⋯)`；
4. 修三个缺陷：(D3) 用**平方范数**（`‖z^a‖² = a!`，Fock/Bargmann 内积）+ 乘积公式，让两侧主项对齐；(D1) 用大权 `w ≈ b = exp(x^ε)`，把 `a/pʰ` 变成 `(a/pʰ − w)₊ = w(x/pʰ − 1)₊`，即 G 的 ramp 本身；(D2) 用二次特征 `1 − χ_d` 把“惯性素数”写成“全部素数减一个 L 函数”；
5. 清账与平衡：误差 `x/m + m`，取 `m ≈ √x`。

**真正的心脏是 (I.32)**：`e log p ≤ log ‖T‖ + μmax(M) − μ(L)`（平方范数下整体乘 2），其中 `μ` 是格的斜率。这是“整除（离散、整数）≤ 大小（连续、实数）”的桥，与我们 `aNegativeDim_le` 是同一个形状的命题——但对象完全不同：他们是数域上的 `o`-模、covolume、分式理想的舍入代价；我们是 `Matrix n n ℂ` 上的惯性指数。

**对我们的直接后果**：`stage_4` 里的 `weil_explicit_formula`、`aSignature_*`、`weilGram_*`、`weilZeroDiag`、双曲 Laplacian 那一条链，是 **Weil/Lax–Phillips 正性路线**，与这条最终证明**平行而不相交**。此前把它描述成“与 Alpöge–Claude 对齐”是错的，必须改口径：它是我们自己的（经典）路线，不是这条证明的内核。它是合法的数学，但不是他们的数学。

### 修正 2：指数 1/2 的确切来源是预算平衡，不是谱间隙

`x/m` 是链两端格尺寸误差（增益收 m 次，故除 m）；`m` 是 m 步累积（每步预算随 m 增长，故归一后剩 m）；`xm/k`、`k/n²` 是辅助参数的代价（`k ≈ x^{9/2}`、`n ≈ x^{2}`）。`x/m` 与 `m` 在 `m = √x` 处平衡，各得 `√x`——这就是 1/2。论文还明说：若第二步是 `m²` 而非 `m`，只能到 `Re s > 2/3`。

这条对我们的意义是**方法论**：`stage_4` 的主链七条全带 `sorryAx`，而且**没有任何显式误差项**。他们的每个 `[quoted]` 都带着一个可核算的预算式；我们的 sorry 是黑箱。要把 sorry 变成“义务”，先要有预算式。

### 修正 3：“(M) is not proved here” 的准确含义

论文的边界表（Part III 开头）分三档：proved / proved conditionally on statements of the source / quoted。逐条：

| (M) 的组成 | 论文状态 | Lean 侧我们定位到的名字 |
|---|---|---|
| 体积分性 + 赋值陈述（hypothesis (B)） | §III.5 写出，但**以 (B) 为前提**；(B) 本身取自 source | `BHyp`、`de1`/`de2`、`letterLog`、`Quant`、`weightQuantization`、`asmS_diff` |
| 大小界的算术输入（内积公式、covolume、局部指数界、层间过渡） | §III.7 证明“由 11 条具名输入推出”，11 条本身 quoted | 论文点名 `InnerProductFormulaC` 等 |
| 迹公式估计（相对迹公式、近似正交） | §III.8 证明“维数界由 3 条 source 陈述推出”，3 条 quoted | — |
| Galois 上同调的界（Vandiver 的弱化） | §III.9 证“由界到分母的界”，界本身 quoted | `shaLen`、`VVle`、`VWin`（`ExistsPageN.lean:49`） |
| 映射与权的构造 + (M) 的组装 | **not yet begun** | `ASK`、`MAIN`、`AskMainBalance`、`colour_balance` |

关键一条：**(M) 在 Lean 里不是空洞**。我们定位到

- `AskMainBalance`（`Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:98`）是一条 `def … : Prop`，内容是 `(ASK − MAIN) = De`，正是论文 Part II (5.3) 那条**精确恒等式** `P − M = Σ_i w_i R_i(a/w_i)`；
- 它由 `theorem colour_balance : AskMainBalance (H := H) := by`（`…/ChainSlopeWindows/StronglyIrreducible.lean:695`）承担，全库 0 sorry。

所以边界应这样写：**人类可读的证明缺 (M)；形式层不缺，但形式层本身未过同行评审，且我们无法在本机复核定理层**（175,187 模块、峰值 6.4–7.8 GB/进程、本机提交上限 39.7 GB，见 `Build_Feasibility.md`）。三档可信度必须分开说，不能笼统说“已证/未证”。

---

## 3. 逐条映射表（我们的资产 ↔ 论文对象）

| # | 论文对象 | 我们的对象 | 关系强度 | 可复用性 |
|---|---|---|---|---|
| 1 | (I.6)/(I.32) 整除 ≤ 大小 | `aNegativeDim_le`（`stage_4`） | 同形：离散指数 ≤ 连续大小 + 指数修正 | 形可复用，算术内容不可 |
| 2 | III.6 Thm L4“粘合的格”：斜率 = 增益总和 − 损失 | `hasSignature_fromBlocks` | 同一个代数动作：分块组装下指数可加 | **骨架可复用**（我们 30 条声明里最贴的一条） |
| 3 | III.6 Lemma L5：秩下降时的斜率界 | `aNegativeDim_le` + `card_eq_of_hasSignature` | 秩/维数亏损控制负部 | 形可复用 |
| 4 | (I.16)(I.17)：`‖z^a‖² = a!`，Cauchy–Schwarz 定大小 | `phiHat_sq_le`（`WeilGramConcrete`，常数 `(exp T)²`） | 同一个“大小侧”，**我们选的范数极差** | **本轮已改**：`WeilGramSharp` 把上半平面的 `exp‖ρ‖` 降成 `1` |
| 5 | (I.25) `P = Σ Σ(1−χ_d(pʰ)) log p (a/pʰ − w)₊` | `weilPrimeGram`（权 `p^{−x}`） | 同一对象，**我们用了错权** | 应换成 `primVal`（Frobenius 轨道 cosetMean）；重 |
| 6 | (I.26) `M = a(log a − 1 − γ + L'/L(1,χ_d) − ⟨log w⟩)` | **无** | 我们连主项都没写 | 缺；但 `MAIN` 就是现成模板 |
| 7 | §I.8 误差预算 `x/m + xm/k + m + k/n²` | **无** | `stage_4` 无任何显式误差项 | 应引入；模板见下 |
| 8 | §I.1 Landau 单边引理（含区间版，Part II §1 一页证完） | **无** | 独立的、可低成本形化 | 候选（不依赖 (M)） |
| 9 | `G(x)`、`G_χ(x)`、`G_ψ(x)`（§I.10 一次处理全部 Dirichlet L） | `G χ x`（QRH/GRH 口径） | 同一统计量族；他们覆盖 GRH 全域 | 口径可对齐，正是我们 GRH 层该说的话 |
| 10 | `GrowthBoundGivesRiemannHypothesis`（[6]，184 行） | 无 | “窗口 + 不等式 ⇒ 增长界 ⇒ RH”的**终段模板** | **最值得抄的骨架** |

### 3.1 `ASK` / `MAIN` 与论文 (I.25)/(I.26) 的逐字对应

`FirstPrimeNeSecondPrime.lean`：

```lean
def ASK (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ :=
  (∑ p ∈ (range (N + 1)).filter (IsInert D), 2 * Real.log p * askP D N a t w p)
   + Real.log D.d * askD D N a t w
```
其中 `askP` 的每一项是 `max (a / p^i − w (partner t g)) 0`；`2 log p` 只对**惯性**素数取。这正是 `(1 − χ_d(pʰ)) = 2`（惯性且 h 奇）与 `0`（其余）的展开，`log D.d` 那一项对应“d 自身单独处理”。

```lean
def MAIN (ell …) (a : ℝ) (w : E0 × H → ℝ) : ℂ :=
  a * ((log a − 1 − γ) + ell chC − (1/|Φ|) ∑ ρ ∈ ΦSet, log (w ρ))
```
即论文 `(I.26)`，`ell chC ↔ L'/L(1, χ_d)`，`⟨log w⟩` 是 2n 个格上的平均。

**由此可得一条可写进摘要的硬话**：论文 (I.25)/(I.26)/(5.3) 与归档 `ASK`/`MAIN`/`AskMainBalance` 是**同一组对象**，且 (5.3) 已被 `colour_balance` 无条件证掉（形式层意义下）。这不是“相似”，是同一份东西的两种写法。

---

## 4. 本轮已落地的一条改进（不是提案，是编译过的定理）

`OrderPreservingBijection/WeilGramSharp.lean`（import `WeilGramConcrete` 的 olean，独立模块，不动主文件）：

上半平面 `0 ≤ Im ρ` 上，相位 `e^{Iρx}` 的模是 `e^{−(Im ρ)x} ≤ 1`（`x ≥ 0`），所以在那里 **`exp‖ρ‖` 是多余的**：

| 定理 | 内容 |
|---|---|
| `phase_re_eq` | `(I·ρ·x).re = −(Im ρ)·x` |
| `phase_norm_le_one` | `0 ≤ Im ρ, 0 ≤ x ⇒ ‖e^{Iρx}‖ ≤ 1` |
| `phiHat_norm_le_one` | `‖φ̂(ρ)‖ ≤ ∫₀¹‖φ‖`（不带 `exp‖ρ‖`） |
| `phiHat_sq_le_one` | `‖φ̂(ρ)‖² ≤ (∫₀¹‖φ‖)²` |
| `weilZeroDiag_re_le_upper` | `hz_j ≤ card S · (∫₀¹‖φ_j‖)²` |

对照旧版 `weilZeroDiag_re_le`：`card S · (exp T)² · (∫‖φ‖)²`。在零点高度 `γ ~ 10¹²` 的量级上，`e^{2γ}` 对 `1` 的差是纯粹的垃圾项——这就是论文 (I.16) 教的同一件事：**先把范数选对，大小侧才是可用的**。

编译与审计（`_wgs_out.txt`，exit 0，零警告）：

```
phase_re_eq / phase_re_nonpos / phase_norm_le_one / phiHat_norm_le_one /
phiHat_sq_le_one / weilZeroDiag_re_le_upper
  → 全部 [propext, Classical.choice, Quot.sound]
```

硬边界（不许省略）：只做上半平面；下半平面要靠“`S` 与共轭配对”或对 `φ` 实值性假设，未写；对角截断与 `j ≠ k` 交叉项的缺失照旧。

---

## 5. 边界：这篇论文自己承认没证的，和我们仍然做不到的

**（M）内部的五条（论文原话：`is not proved here`）**

1. θ 核在 height-two 对数坐标下的整性，以及建在其上的赋值陈述（即 (B)）；
2. 大小界的算术输入：θ 提升的内积公式及其局部因子、格的 covolume、局部指数界、层间过渡；
3. 迹公式估计本身；
4. Galois 上同调的界本身（Vandiver 的弱化；论文说 Lean 里依赖 Ferrero–Washington 的 µ-不变消失、Kato Euler system、模性提升）；
5. 映射与权的构造、以及 (M) 的组装（“not yet begun”，§III.6 只做了 model case）。

另有两条同级的：§III.4 有**四处 passage 是条件性**的（参考均值、提升的特征值、逐行比较、链末配对）；`T`/`T₂` 已构造但“它们在 (M) 里的用法尚未写出”。

**我们仍然做不到的**

- 定理层 `#print axioms riemannHypothesis`：本机不可达（内存），只能做 `Statements` 单编替代；
- 1,478,198 条声明这个数：无 olean 级闭包，核不了；
- 任何“这个证明是对的”的判断：我们只能核“文本层干净 + 引用可落行 + 终端桥存在”，不能核数学正确性。

---

## 6. 下一步（按意义排序，每条标明代价）

1. **补完 `hz` 的解析界**（半天）：下半平面用共轭配对（`φ̂(ρ̄) = conj φ̂(ρ)`，当 `φ` 实值），再写 `j ≠ k` 交叉项的一行界 `|⟨φ̂_j, φ̂_k⟩| ≤ …`。收益：`hz` 从“带 `e^{2T}` 的垃圾界”变成真界，`aNegativeDim_le` 的前提才不是空的。
2. **引入预算式陈述模板**（1–2 天）：照 [6] 的形状写 `SizeWindows ∧ (nT·m·b·δ/2)·(G − 4x^{1/2+ε}) ≤ Err + 2·nT·m·b/x ⇒ G ≤ x^{1/2+(C+3)ε}`。收益：把 `stage_4` 的七条 `sorryAx` 从黑箱变成“带误差项的义务”，这是唯一能让 sorry 有意义的结构改动。
3. **素数侧换权**（3–5 天，重）：`weilPrimeGram` 的 `p^{−x}` 换成 `primVal` 型的 `cosetMean (inertia p) (i • frob p) ψ`。先做一个素数的玩具例子（`ZMod 2` 上 cosetMean 就是一维平均）验证形状。收益：这是唯一“数学上正确”的权，也是我们此前自己标出的硬边界。
4. **形化 Landau 单边引理（区间版）**（2–3 天，独立）：Part II §1 是一页证明，用 F 的高阶导数只“看”一个区间；不依赖 (M)。收益：一个真正可交付、可审计的 RH 相关定理，且与我们既有链无关。
5. **搬 L5 型“秩下降 ⇒ 负部界”**（1 天）：`aNegativeDim_le` 已有，只差把“秩”接成 `Finset.card` 与子空间维数。
6. **GRH 侧口径**：把 `G_ψ`（§I.10 的 `G(y) + (1/(3o+1))Σ Re G_{ψ^j}(y)`）写成我们对全部 Dirichlet 特征的统一统计量。收益：把 QRH/GRH 的“数据”与“定理”分层写清楚。

---

## 7. 数据 / 定理 / 传闻 的三层标注（写给未来的自己）

- **数据**（可复算）：SHA-256、175,187、17,374,215、1,066,087、静态扫描全 0、29/29 路径、`VWin` 在第 49 行。
- **定理**（有条件）：`AskMainBalance` 由 `colour_balance` 证；`ASK`/`MAIN` 是论文 (I.25)/(I.26) 的同物；`WeilGramSharp` 六条上半平面界（axiom 已打印）。
- **传闻**（不可核）：1,478,198 条声明；“17 million lines”对应 25 万页；“已证 RH”这个整体判断。
