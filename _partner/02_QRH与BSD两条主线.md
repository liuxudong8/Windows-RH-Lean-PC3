# QRH 与 BSD 两条主线

## 现状、已机检的部分、未证的部分，以及与 Alpöge–Claude 论文的接口

编制：2026-11-23　|　工具链：Lean 4 `v4.34.0-rc2` + mathlib（`lake build QRH` **3836 jobs 全绿、0 error**；命名 axiom **10** 条、opaque **3** 个、明确登记的未形式化项 **1** 条；`BSD` 库仍为 2026-10-06 口径 16 条，未重审）

---

## 0. 一页结论

1. **两条线的对象与黎曼猜想不同层级，不重叠、互不替代。** QRH 研究 L(s, χ₅) 的**零点局部配对统计**（常数 A(λ) → 1）；BSD 研究椭圆曲线 L 值的**算术**（37a1 的弱 BSD：`mwRank = analyticRank`）。黎曼猜想被证或被否，都不改变这两条线的研究对象。
2. **两条线都挂在 GRH / Dirichlet-L 这一层**，这恰好是 Alpöge–Claude 论文 §I.10 一次覆盖的范围（它一次处理全部 Dirichlet L，不止 ζ）。因此论文对我们的推动不在「路线」，而在**接口**：它把 GRH 从「假设」变成「可能被机检的语句层」。
3. **最实在的一条（已收窄）**：QRH 卡住的数论假设里，真正需要外部零点的只剩 **2 条**（`N_L_lower_bound` 零点计数下界、`pair_count_bound` 竖直邻域配对计数）。原先台账中的 `zerosLChi5_bounded_finite` 已**真证**（无条件定理，零 axiom），`N_L` 已从「数据型 axiom」降为**真实定义**（`Set.ncard` 零点计数）。若对方的 GRH 语句层可对 χ₅ 实例化，这 2 条可从「分析估计」降级为「标准计数」——**这是唯一一条能真正缩短我们假设清单的外部输入。**
4. **我们比对方缺一个层级**：他们把主分解做成了定理（`AskMainBalance`，全库零 sorry），我们把同类分解还是假设（`bgs3_pair_expansion`）。这一步之差决定审稿人第一句话问什么。**2026-11-23 已把它的语句口径修正**（详见 §3.2），但「假设 → 定理」仍未完成。

---

## 1. QRH 是什么

**目标**：证明 L(s, χ₅) 单族配对常数 A(λ) → 1。这是「拟随机假设（QRH）常数机制」的唯一现实通道：QRH 常数 0.6725 → 7/8 需要 A ≤ 1.125，而 A → 1 远强于 A ≤ 1.125，一次性打通。

| 项 | 内容 |
|---|---|
| 配对常数 | A_L(K) = 1 + (Σ_{z₁≠z₂∈Z_T} K(δ·im(z₁−z₂))²) / N_L(T)，δ = log T / 2π，Z_T = 临界带零点 ∩ {\|Im\| ≤ T} |
| 零点计数 | N_L(T) := #Z_T（**真实定义**，`Set.ncard`；不是假设的算子） |
| 常数机制 | C_MT = 1/2 + (1/√2)·cot(1/√2) = 1.3274992963；QRH 常数 0.6725 = 2 − C_MT |
| 判定 | A ≤ 1.125 ⟺ 7/8 成立（7/8 为既定目标，31/32 已被否） |
| 数值现状 | Fejér 窄核 λ → 0 极限 A → 1.0079（T = 6×10⁵）；窄核专项推进后 A ≈ 0.990；5 子区间漂移 ≤ 0.005 |

**口径纪律**：A 是**数据**，不是定理；「证到 1」不等于接近黎曼猜想（统计口径与实际描述是两件事）。

## 2. QRH 已经机检过的部分（这些是真定理）

| 定理 | 内容 | 状态 |
|---|---|---|
| `C_MT_lt_four_thirds` | C_MT < 4/3 | **真证**，纯有理链（cos 四阶上界 73/96、sin 五阶下界、√2 全程消去、无积分、无聚合依赖） |
| `fourierCos` | 傅里叶余弦核 | **真定义**（Bochner 积分，不可积惯例取 0） |
| `fourierCos_scale` | 频域缩放律 | **真证** |
| `khat_lipschitz` | 核函数的 Lipschitz 常数 L = π/(√2·\|sin(1/√2)\|) ≈ 3.42 | **真证**（含奇点延拓口径修正） |
| `prime_weight_bounds_Khat` | 素数权重双界 \|b_n\| ≤ M·n^(−1/2)、\|Δb_n\| ≤ M·n^(−3/2)，M = L·δ + B | **真证** |
| `prime_sum_bound` | 素数项 Abel + SW 组装界 | **真证**（SW 本体仍为假设） |
| `f0_sub_feps_L1_bound` | ‖f₀ − f_ε‖₁ ≤ 2ε·(√2\|sin(1/√2)\|)^(−1) | **真证**（7 个辅助件） |
| `pair_const_eps_bias` | 配对常数偏差，C₁ = 4M²D | **真证** |
| `pairCount_L1_bound` | 离散配对和 ≤ D·N_L(T)·‖g‖₁ | **真证**（截断零点集口径修正后） |
| `n2_linkage` | ε–λ 联动：λ=(log T)^q、ε=c(log T)^(−q) ⟹ 偏差 O((log T)^(−q))，C = 2cM | **真证** |
| `zerosLChi5_bounded_finite` | 截断零点集 Z_T 有限（任意 T） | **真证**（搬运归档 `DirichletLZerosInWindowFiniteAndPosOrder`，无条件、零 axiom） |
| `lfun_conj_symm` | L(conj s) = conj(L s)，**全平面** | **2026-11-23 由 axiom 降为定理**（解析延拓唯一性，mathlib `riemannZeta_conj` 同款；见 `LFunction_conj_global`） |
| `s71_main` | 主定理：A_L(K) ≤ C_MT + C₁ε + C₂，C₂ = 2 | **组装真证**（口径已改为 `N_L T` + `Z_T`） |

配套的**真实定义件**（把此前 opaque 换成 mathlib 对象或显式构造，均无 axiom）：

- `LFun := DirichletCharacter.LFunction chi5Dirichlet`（mathlib 的 Hurwitz-ζ 线性组合解析延拓，`DirichletContinuation.lean:61`）；
- `chi5 : ℕ → ℝ := fun n => (chi5Dirichlet (n : ZMod 5)).re`，并证 `chi5_eq_chi5Dirichlet`（实值投影无损）；
- `vonMangoldt := ArithmeticFunction.vonMangoldt`、`logDerivTerm r := (logDeriv LFun r).re`；
- `N_L(T) := (Z_T).ncard`、`zerosLChi5UpTo T := {z | z ∈ zerosLChi5 ∧ |z.im| ≤ T}`（均在 `S7_1_Main`，Stage3 经 import 使用）。

构建状态：`lake build QRH` **3836 jobs、0 error**（2026-11-23），mathlib HEAD `f8d25bb`（本机缓存不全，只能逐模块 import）。

## 3. QRH 还没证的部分（如实清单）

### 3.1 命名 axiom：10 条

| 类 | 位置 | 假设 | 实质 | 可缩短性 |
|---|---|---|---|---|
| **D** | `S7_1_Main:1145` | `bgs3_pair_expansion` | 配对展开分解 A_L = diag + prime + offcrit | **最该消灭的一条**：它本身是组合恒等式，应当可证（口径已修正，见 3.2） |
| A | `S7_1_Core:705` | `fourierCos_Khat` | 核函数与解析式的连接件 | 定义一致性，工程（需实算 Bochner 积分） |
| A | `S7_1_Main:345` | `bgs5_khat_fourier_supp` | 频域窄支撑（积分层） | 工程 |
| B | `S7_1_Main:312` | `siegel_walfisz_chi5` | PNT-in-AP 量级（模 5） | 外部定理，短中期无望 |
| B | `S7_1_Main:180` | `landau_explicit_L` | Landau/Weil 显式公式 L 版 | 外部定理 |
| B | `S7_1_Main:1176/1179/1185` | `bgs4_offcrit_split` / `_low` / `_high` | 离线项切割分解 + 两段 √log 界 | 依赖 3 个 opaque（见 3.4） |
| **C** | `S7_1_Stage3:738` | `N_L_lower_bound` | 零点计数下界 c·T·logT ≤ N_L(T)（RvM 方向） | **GRH-χ₅ 接口可降级**；无接口则需 RvM 计数（幅角原理），属长线 |
| **C** | `S7_1_Stage3:745` | `pair_count_bound` | 竖直差带内配对总数 ≤ Dcnt·N_L(T) | **GRH-χ₅ 接口可降级** |

分类含义：**A** 结构/连接（无数学风险）、**B** 外部分析定理、**C** 数论计数（最可能被外部输入缩短）、**D** 分解假设（最应主动消灭）。

### 3.2 已修的一处语句层缺陷：`bgs3_pair_expansion` 口径手术（2026-11-23）

旧语句把 `pairConstant` 的第三实参（归一化分母 `N`）写成 `Real.log T / (2π)`，等于**把 δ 当成零点数**；求和域又是整条 `zerosLChi5`（**无穷集**），那个 `∑' p : ℂ×ℂ` 在无穷集上没有意义。修正后：

```lean
pairConstant K δ (N_L T) (zerosLChi5UpTo T) = diag + prime + offcrit ∧
diag ≤ C_MT + C₁ * ε ∧ |prime| ≤ 1 ∧ |offcrit| ≤ 1
```

`pair_sum_expansion`、`s71_main`、根模块自检 `example` 全部同步。语义后果：分母是真实零点计数（与 Stage3 的 `pair_const_eps_bias` 口径统一），求和域是有限截断集（`tsum` 退化为有限和，无需 Summable 假设）。**陈述变强，但「假设 → 定理」仍未做。**

### 3.3 本轮清除的旧账（附理由，供合伙人复核）

| 条目 | 处置 | 理由 |
|---|---|---|
| `lfun_dirichlet_series`（原 `0 < re s` 时的 Dirichlet 级数表示） | **删除** | 命题在 `0 < re s ≤ 1` 区间**为假**（原始级数只在 `re s > 1` 收敛），且全库 0 处使用 |
| `lfun_conj_symm` | **axiom → theorem** | `LFunction_conj_global` 全平面真证（χ 实值 + χ ≠ 1 ⟹ L 整函数 + 解析延拓唯一性） |
| `N_L`（`axiom N_L : ℝ → ℝ`） | **axiom → def** | 数据型假设（「某个函数」）；改为真实零点计数 `Set.ncard`，使 `N_L_lower_bound` / `pair_count_bound` 从「对未知算子成立」变为「对真实计数成立」 |
| `offcritSum` + `n3_remainder_uniform`（N3 离线项一致） | **删除，登记为未形式化** | ① 全库 0 处使用；② 自由算子 + ∃R 有界声明可被 `offcritSum ≡ 0` 满足 ⟹ 空条目；③ 文档对象（S7.5 `Roff = O((logT)^{-1/2})·N_L`，配对公式减去主项的余项）依赖 `w(ρ−ρ')` 权重、复自变量 `r̂`、`x` 尺度相减三件未形式化机制，按字面写原始两两求和会得到 `O((T logT)²)` 而声明 `O(T√logT)` ⟹ 假命题 |

### 3.4 opaque：3 个（BGS 引理 4 机制算子）

`offCriticalError`、`offcritLow`、`offcritHigh`（均在 `S7_1_Main`）。它们不是「未证命题」，而是**未给定义**的算子：其内容由 `bgs4_offcrit_split/low/high` 三条 axiom 刻画。替换成本高于剩余 axiom 清理，属下一轮议题。

### 3.5 明账：1 条未形式化项

**N3（离线项跨 λ 一致）**：登记为「未形式化」，不是「已证」。补真前置三件（引理 5 本体含 `w`/`r̂`、`x` 尺度参数、主项相减口径）全部在「L 版 BGS 假设」层。

---

## 4. BSD 是什么

**目标**：`weak_BSD_37a1 : mwRank E/K = analyticRank E/K`（曲线 37a1 及其五次扭，K 为相应域）。

**当前口径（2026-10-06 审计，尚未重审）**：库 axiom **16** 条（Main.lean 9 + LSeries5.lean 7），主定理数学闭包 **11** 条（另 3 条为 Lean 基础公理），`sorry = 0`，`lake build BSD` exit 0。该审计文档已把 16 条按 A/B/C/D 四类分档——**这是整个项目里最成熟的一份假设台账**，QRH 已照它的格式重做（见 §3）。

| 类 | 数量 | 性质 | 代表 |
|---|---|---|---|
| A | 4 | 结构占位（口径定义，无数学风险） | `analyticRank`、`mwRank`、`GammaUpper`、`ap_E` |
| B | 3 | 数值钉死（LMFDB/Cremona + 独立重检） | `ap_E_values`、`Lprime_E1`、`Lprime_E1_interval`（区间宽，容错充足） |
| C | 9 | 数学已证、mathlib 无理论 | 最深的是 `rank_E5_Q_eq_zero_of_L_E5_ne_zero`（Kolyvagin Euler 系统，已条件化接线） |
| D | 2 | 已消除（axiom → theorem） | `coefficient_bound_aE5`、`summable_fE5` |

**必须声明的时间差**：以上是 2026-10-06 的口径。此后目录里新增了 `RankTwo389`、`ShaFreeLayer`、`ShaPComponent`、`GrHChain389`、`Positivity`/`PositivityGRH`/`ZeroGap` 等模块，**这批尚未重审**。对外引用前必须重跑一次 axiom 闭包审计，否则数字不可信。（QRH 侧的 10/3/1 是本轮实测数字，可直接引用。）

## 5. 两条线共同的形状（与 Alpöge–Claude 论文对照）

| 结构位 | Alpöge–Claude | QRH | BSD |
|---|---|---|---|
| 精确恒等式 | `ASK − MAIN = De`（`AskMainBalance`，**已真证**） | A_L = diag + prime + offcrit（**仍是假设**，口径已修） | 秩界散在 `Main.lean` 的组装里 |
| 主项 | `MAIN = a(log a − 1 − γ + ℓ(chC) − ⟨log w⟩)` | diag ≤ C_MT + C₁ε（C_MT < 4/3 **已真证**） | Heegner 点 / Sha 阶 |
| 素数项 | `ASK = Σ 2 log p[…] + log d·askD` | `primeSum = Σ Λ(n)χ₅(n)n^(−1/2)K̂(δ log n)` | Euler 系统的 Selmer 界 |
| 权重处理 | Abel 求和 + Lipschitz | `prime_weight_bounds_Khat`，M = L·δ + B（**已真证**） | `SelmerDescent` |
| 未证心脏 | `BHyp` 等五类 + (M) 未证 | 10 条 axiom + 3 opaque + N3 未形式化 | 上述 16 条（待重审） |

**读法**：三个项目用的是同一台机器——「把目标量精确拆成主项 + 素数项 + 误差项，再用整除 ≤ 大小压住」。他们把这台机器推到 1,700 万行；我们的体量小两个数量级，但**恒等式这一层我们落后一格**，这是唯一值得追的差距。

---

## 6. 与论文的三个接口

**接口一（最实在）：GRH 对 Dirichlet-L 的语句层。**
论文 §I.10 一次处理全部 Dirichlet L：G_ψ(y) = G(y) + (1/(3o+1))Σ_j Re G_{ψ^j}(y)。对 χ₅ 而言，这正好能供 QRH 的 C 类**两条**假设（`N_L_lower_bound`、`pair_count_bound`）。注意口径：**他们证 GRH 也是 mod (M) 的**，我们要的不是「GRH 为真」，而是「GRH-χ₅ 的形式语句 + 其零点计数推论在 Lean 里可实例化」——这一点是无条件可用的（归档公开，语句层已能单编）。

**接口二：恒等式纪律。**
他们把 `AskMainBalance` 写成精确恒等式并证明（`colour_balance`），我们把它写成假设。技术动作很小：先把 A_L = diag + prime + offcrit 写成等式并证掉，再把三个界接上去。

**接口三：Galois 上同调 ↔ Euler 系统（双向）。**
论文 Part III 列的「Galois 上同调的界」是他们自己承认未证的一项；而我们 BSD 侧已有 `EulerSystem.lean`、`SelmerDescent.lean`、`Sha11_389.lean`、`TwoDescent.lean` 的雏形。**结构上，我们手里有他们缺的那个器官；体量上，我们的只是草图。** 这条接口的价值在于定位，不在于可立即互换。

---

## 7. 四条动作与代价

| # | 动作 | 代价 | 收益 |
|---|---|---|---|
| 1 | 在归档树中定位 GRH/Dirichlet-L 语句与实例化入口，核查能否供 `zerosLChi5` | 低（一次定向检索，当天） | 唯一能**真正缩短假设清单**的动作；失败也有信息（说明通用性有洞，我们的两条反而成为独立贡献） |
| 2 | 把 `bgs3_pair_expansion` 由假设变定理（口径已修，可开工） | 中（需重编全量） | QRH 从「含分解假设」升为「只含分析估计」 |
| 3 | 重跑 BSD axiom 闭包审计，把 2026-10-06 口径更新到含 `RankTwo389`/`ShaFreeLayer`/`GrHChain389`/`Positivity*` | 低—中 | 对外数字可信；否则现在引用的 16 条是过期口径 |
| 4 | BSD 建 `RankBalance` 精确恒等式层（照 `AskMainBalance` 形状） | 中 | BSD 主链第一次有「心脏」形状 |

**建议顺序**：先 1（成本最低、信息量最大），再 3（把对外口径修好，避免合伙人拿到过期数字），再 2 与 4。

## 8. 不做什么

- **不用论文的指数 1/2 记账去改 QRH 的 A → 1**。QRH 的 A 是局部配对统计常数，论文的 G(x) ≤ x^(1/2+ε) 是增长界，两者虽然都叫「窗口」，量纲不同（他们的 x/m + m 是空间预算，我们的 λ = (log T)^q 是频谱预算）。借格式可以，借结论不行。
- **不搬 (M) 的具体算术**（内积公式、covolume、局部指数界、层间过渡）。那需要对方的机器规模。
- **不做追赶式形式化**：复刻一份 RH 形式化毫无意义，那已有 1,700 万行。

## 9. 三层标注（阅读本文档时请按此区分）

| 层 | 含义 | 本文档中的例子 |
|---|---|---|
| **定理（数据来源：机检）** | Lean 编译通过、公理集干净 | `C_MT_lt_four_thirds`、`khat_lipschitz`、`n2_linkage`、`pairCount_L1_bound`、`zerosLChi5_bounded_finite`、`lfun_conj_symm` |
| **数据（数值实测）** | 算出来的数，不是证出来的 | A → 1.0079、A ≈ 0.990、漂移 ≤ 0.005、L′(E,1) ∈ [0.30599977, 0.30600000] |
| **传闻/第三方声明** | 未经我们复核 | 「Claude 证出黎曼猜想」「25 万页文本」等媒体表述 |

**第四层（本文档新增，必须与上面三类分开读）**：`axiom` 10 条 + `opaque` 3 个 + N3 未形式化 = **已知的洞**，位置与理由逐条列在 §3；它们既不属定理，也不属数据。

---

## 附录：文件与复现

- QRH：`C:\proj2\QRH\{S7_1_Core,S7_1_Main,S7_1_Stage3}.lean`，根 `C:\proj2\QRH.lean`，权威口径 `QRH_summary.md`
- QRH 上游搬迁件：`C:\proj2\OrderPreservingBijection\{Chi5Real,LSeriesConj,Exceptional\}`（χ₅ 实值件 8 条、L 级数共轭 5 条、例外零点接口 30 文件，公理集均实测干净）
- 审计原始输出：`_chi5real_ax.txt`、`_conj_ax2.lean`、`_conjglobal_ax.lean`、`_nl_ax.lean`、`_n3_ax.lean`、`_s71_ax.lean`、构建日志 `build_qrh_H/I/J/K/L.txt`
- BSD：`C:\proj2\BSD\`（`EulerSystem`、`SelmerDescent`、`TwoDescent`、`Sha11_389`、`RankTwo389`、`GrHChain389` 等），审计口径 `BSD_axiom_audit.md`，总述 `BSD_summary.md`
- 论文对照：`Alpoge_Paper_Compare.md`（十项映射表 + 三条口径修正）
- 仓库：`github.com/liuxudong8/Windows-RH-Lean-PC3`
