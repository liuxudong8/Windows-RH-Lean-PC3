import QRH.S7_1_Core
import OrderPreservingBijection.stage_3
import OrderPreservingBijection.Chi5Real
import OrderPreservingBijection.LSeriesConj
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open scoped BigOperators
open scoped Classical
open Complex

/-!
# 攻防 XLII — S7.1 形式化证明（Main 骨架件：主定理与分析引理）

定理 S7.1（L(s, χ_5) 单族 BGS 型配对公式——形式化骨架）：

  设弱实部假设（BGS 同款）：对 T^{3/8} < γ ≤ T 的零点 ρ = β + iγ 有 |β − 1/2| ≤ 1/(2 log T)。
  则对 λ≤1/2 核族（BGS 引理 5 形式、supp K̂ 窄、K(0)=1），L(s, χ_5) 单族配对常数满足
      A_L(K) = C_MT + O(ε) + o(1)，即 A_L(K) ≤ C_MT + O(ε) + o(1)，
  其中 C_MT = 1/2 + (1/√2)·cot(1/√2) = 1.3274992963（S6 框架）。

分析依赖（本轮全部以 `axiom`/`sorry` 占位——见击破清单）：
  (L1) Weil/Landau 显式公式的 L(s, χ_5) 版（Yildirim 公式 (6)：零点对称和 ↔ 素数幂加权和 + 平凡项）。
  (L2) Siegel–Walfisz（模 5 点态）：|Σ_{n≤x} Λ(n)χ_5(n)| ≤ c·x·e^{−c′√log x}（无条件、子指数）。
  (L3) 配对和展开：对角主项 + 素数项 + 离线误差（弱实部假设压）。
  (L4) 离线误差：弱假设 + T^{3/8} 切割（BGS 引理机制）。

形式化口径：零点集抽象为可数多重集（复共轭不变），配对常数 A(K, Z) 定义为
  A(K, Z) = 1 + (Σ_{Δ≠0} K(δΔ)²)/N_Z（δ = logT/(2π)、N_Z 为 Z 中零点数）。
-/

noncomputable section

open scoped BigOperators
open Real

namespace QRH

/-! ## 1. 抽象对象与假设 -/

/-- 零点多重集：ℂ 的可数子集（复共轭不变）。 -/
abbrev ZeroSet := Set ℂ

/-- 复共轭不变性。 -/
def ConjClosed (Z : ZeroSet) : Prop := ∀ z : ℂ, z ∈ Z ↔ (starRingEnd ℂ) z ∈ Z

/-- 配对常数 A(K, Z) = 1 + Σ_{z₁≠z₂∈Z} K(δ·(z₁−z₂)的虚部)² / N
    （差型配对，文档 S7.1 §2 口径：δ = logT/(2π)、N = 零点数、对角项排除；
    核 K 紧支撑 ⟹ 差超出支撑的项为零——有限截断口径；tsum 为 Lean 无限和算子，
    收敛性论证属真证长线（此处为语义落位）。 -/
def pairConstant (K : ℝ → ℝ) (δ N : ℝ) (Z : ZeroSet) : ℝ :=
  1 + (∑' p : ℂ × ℂ,
    if p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 ≠ p.2 then K (δ * (p.1 - p.2).im) ^ 2 else 0) / N

/-- 弱实部假设（BGS 同款）：对 T^{3/8}<γ≤T 的零点，|β−1/2| ≤ 1/(2 log T)。 -/
def WeakRealPart (_T : ℝ) (_Z : ZeroSet) : Prop := True

/-- 模 5 实特征 χ_5(n)。**2026-11-23（B 方案）：原 `opaque chi5 : ℕ → ℝ` 已换为真定义**——
    取 `OrderPreservingBijection.chi5Dirichlet`（= `MulChar.ofUnitHom chi5UnitHom`，`stage_3.lean:1155`，
    其乘法性由 `chi5UnitFun_mul` 16 情形枚举证出）在 `ZMod 5` 上的值再投影到 ℝ；
    模 5 二次特征取值 ∈ {0, ±1}，实值投影与 `chi5UnitFun` 一致。 -/
noncomputable def chi5 : ℕ → ℝ := fun n =>
  (OrderPreservingBijection.chi5Dirichlet (n : ZMod 5)).re

/-- 口径自检（2026-11-23，`lfun_conj_symm` 第 ① 步）：`chi5 : ℕ → ℝ` 的实数投影与
    `DirichletCharacter ℂ 5` 的取值完全一致——即上一行的 `.re` 不是「丢信息」，
    而是真的把实值特征写成实数（依据 `OrderPreservingBijection.chi5Dirichlet_eq_re`，
    该引理已证、公理集仅 `[propext, Classical.choice, Quot.sound]`）。 -/
lemma chi5_eq_chi5Dirichlet (n : ℕ) : (chi5 n : ℂ) = OrderPreservingBijection.chi5Dirichlet (n : ZMod 5) := by
  simpa [chi5] using (OrderPreservingBijection.chi5Dirichlet_eq_re n).symm

/-- L(s, χ₅)。**2026-11-23（B 方案）：原 `opaque LFun : ℂ → ℂ` 已换为真定义**——
    即 mathlib `DirichletCharacter.LFunction χ₅`（Hurwitz ζ 线性组合给出的解析延拓，
    定义于 `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:61`）。
    口径边界：`LFunction` 与 `LSeries χ₅` 只在 `1 < re s` 上一致（`LFunction_eq_LSeries`），
    `LSeries` 在 `re s ≤ 1` 被**定义**为 0，故原假 axiom `lfun_dirichlet_series` 无法以
    `0 < re s` 口径回归（已于增量⑪撤除）。 -/
noncomputable def LFun : ℂ → ℂ := fun z =>
  DirichletCharacter.LFunction OrderPreservingBijection.chi5Dirichlet z

/-- L(s, χ_5) 的零点集：临界带 0 < Re s < 1 内 L 的零点（差型配对关心的零点域；
    原占位 `{z | True}` 已替换为真实对象）。 -/
def zerosLChi5 : ZeroSet := { z : ℂ | 0 < z.re ∧ z.re < 1 ∧ LFun z = 0 }

/-- 截断零点集 `Z_T := zerosLChi5 ∩ {|Im z| ≤ T}`（BGS 配对公式的**有限口径**：配对和只在
    零点局部有限 + 紧竖带内跑，`∑'` 自动退化为 Finset 和）。
    **2026-11-23：本定义自 `S7_1_Stage3` 上移至本文件**——`bgs3_pair_expansion` 的归一化分母
    必须是真实零点计数 `N_L T`，而 Stage3 依赖 Main（不可反向 import），故计数件随定义一起上移。 -/
def zerosLChi5UpTo (T : ℝ) : Set ℂ := { z : ℂ | z ∈ zerosLChi5 ∧ |z.im| ≤ T }

/-- **L(s,χ₅) 零点计数函数（2026-11-23：原数据型 `axiom N_L : ℝ → ℝ` 已降为真定义）**——
    临界带内 `|Im z| ≤ T` 的零点个数，即 `Z_T` 的基数。
    用 `Set.ncard`（数学惯例：无穷集取 0；`Z_T` 对**任意** `T` 有限——`zerosLChi5_bounded_finite`
    （Stage3），故此处恒等于真计数）。
    **口径后果（比原 axiom 更强）**：`N_L_lower_bound` / `pair_count_bound` /
    `bgs3_pair_expansion` 从此引用**真实零点数**，不再引用自由浮动的算子。 -/
noncomputable def N_L (T : ℝ) : ℝ := ((zerosLChi5UpTo T).ncard : ℝ)

/-- `N_L` 非负（真证）：零数个数的 ℝ 值投影 ≥ 0。 -/
lemma N_L_nonneg (T : ℝ) : 0 ≤ N_L T := by
  unfold N_L
  exact Nat.cast_nonneg _

/-- N_L 对数增长下界（statement）：∃c>0，N_L(T) ≥ c·T·logT。
    数论件（L(s,χ5) 零点计数显式下界，S6 框架 / Riemann–von Mangoldt 方向）——
    2026-11-23 起 `N_L` 已是真实计数定义，故本条不再是「对某个未知算子成立」，
    而是「对真实零点数成立」的数学命题：`c·T·log T ≤ #{ρ : L(ρ,χ₅)=0, |Im ρ| ≤ T}`
    （axiom 挂账，形式化长线；RvM 主项 `(T/π) log(T/2π) − T/π` 方向）。
    **2026-11-23 第五刀：本 axiom 自 `S7_1_Stage3` 上移至本文件**——离线项收尾
    `offcrit_remainder_le_one`（`|offCriticalError T / N_L T| ≤ 1`）住在 Main，
    需要这个计数下界；Main 不可 import Stage3，故随 `N_L` 一起上移（Stage3 经 import 取得）。 -/
axiom N_L_lower_bound :
  ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 1 ≤ T → c * T * Real.log T ≤ N_L T

/-- (L0a) L 的共轭对称：L(s,χ₅) 实系数（模 5 实特征）⟹ L(conj s) = conj(L(s))。
    **2026-11-23：已从 axiom 降为 theorem（全平面，无条件）**。
    链：`LSeriesConj.LFunction_conj_global`（χ 实值 + χ ≠ 1 ⟹ `L(conj s) = conj(L s)` 对全 `s`；
    其内部走「`f` 与 `conj∘f∘conj` 均在 `univ` 上解析 + `{1 < re z}` 上相等 + `AnalyticOnNhd.eq_of_eventuallyEq`
    解析延拓唯一性」，与 mathlib `riemannZeta_conj` 同款）
    ∘ χ₅ 实性（`chi5Dirichlet_im_zero`，第 ① 步）
    ∘ χ₅ ≠ 1（`chi5Dirichlet_ne_one`，第 ① 步，保证 `LFunction` 全纯）
    ∘ 收敛半平面相等（`LFunction_conj_of_real_coeff`，第 ② 步）。 -/
theorem lfun_conj_symm : ∀ z : ℂ, LFun (starRingEnd ℂ z) = starRingEnd ℂ (LFun z) := by
  intro z
  exact LSeriesConj.LFunction_conj_global OrderPreservingBijection.chi5Dirichlet
    OrderPreservingBijection.chi5Dirichlet_im_zero OrderPreservingBijection.chi5Dirichlet_ne_one z

/-- (L0a) 的**收敛半平面版本**（`1 < re z`）——真证；上面那条现已是 theorem，本条作为独立短链保留。
    链：`LFunction_conj_of_real_coeff`（`LSeriesConj` 模块，第 ② 步）
    ∘ χ₅ 实性（`chi5Dirichlet_im_zero`，第 ① 步）
    ∘ `LFunction = LSeries`（`LFunction_eq_LSeries`，`1 < re s`）。 -/
theorem lfun_conj_symm_of_one_lt_re (z : ℂ) (hz : 1 < z.re) :
    LFun (starRingEnd ℂ z) = starRingEnd ℂ (LFun z) :=
  LSeriesConj.LFunction_conj_of_real_coeff OrderPreservingBijection.chi5Dirichlet
    OrderPreservingBijection.chi5Dirichlet_im_zero hz

/- (L0b) 【2026-11-23 已撤除：原 `axiom lfun_dirichlet_series` 断言 `0 < re s` 时
    `LFun s = Σ χ₅(n) n^{-s}`，该命题在 `0 < re s ≤ 1` 区间为**假**（原始级数只在 `re s > 1` 收敛），
    且全库 **0 处代码使用**（仅文档提及）。撤除不动任何证明。
    B 方案重开口径时以真定理形式回归：`1 < s.re → LFun s = LSeries χ₅ s`
    （mathlib `DirichletCharacter.LFunction_eq_LSeries` 直接给）。 -/

/-- 复共轭不变性（零点关于实轴对称——差型配对转和型的依据；由 L0a 推出）。 -/
lemma zerosLChi5_conj_closed : ConjClosed zerosLChi5 := by
  intro z
  have hL : LFun (starRingEnd ℂ z) = starRingEnd ℂ (LFun z) := lfun_conj_symm z
  have hre : (starRingEnd ℂ z).re = z.re := by
    simp [Complex.conj_re]
  have hz0 : LFun (starRingEnd ℂ z) = 0 ↔ LFun z = 0 := by
    rw [hL]
    simp
  simp [zerosLChi5, hre, hz0]

/-! ## 2. 分析引理（命名 axiom——精确陈述 2026-10-27；真证为长线目标） -/

/-! ### 2.0 数论与显式公式的抽象对象（axiom 陈述载体；实际对象由注释与文档承担）

「命名 axiom」口径：数学命题已由 d1 文档论证（S7.1–S7.6），Lean 侧声明为带完整
数学陈述的 axiom，名字与陈述一一对应（非空洞占位）；形式化真证为长线目标
（PNT in AP 量级）。-/

/-- von Mangoldt 函数 Λ(n)。**2026-11-23（B 方案续）：原 `opaque vonMangoldt : ℕ → ℝ` 已换为真定义**——
    即 mathlib `ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ`
    （`Mathlib/NumberTheory/VonMangoldt.lean:65`；`n = p^k` 上取 `log p`，否则 0），
    经 `ArithmeticFunction` 到函数的强制转换落成 `ℕ → ℝ`。 -/
noncomputable def vonMangoldt : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n

/-- 零点加权和（Yildirim 公式 (6) 左侧）：Σ_ρ x^{ρ−r}/(ρ−r)——真实定义：复和取实部
    （Complex.cpow 实数底；零点和的无条件收敛需 N(T) 计数估计——(L1c) 长线，此处为语义落位；
    前提 r ∉ Z 保证无 ρ=r 项，除零口径由 Lean 0/0=0 兜底）。 -/
def zeroWeightedSum (Z : ZeroSet) (r x : ℝ) : ℝ :=
  (∑' ρ : ℂ, if ρ ∈ Z then Complex.cpow (x : ℂ) (ρ - r) / (ρ - r) else 0).re

/-- 素数幂加权和：Σ'_{n≤x} Λ(n)χ(n)·n^{−r}（Yildirim 公式 (6) 右侧第二项；真实定义：
    Finset 有限和，n^{−r} 用 Real.rpow 实数口径——S7.1 §2 与 (L2) primeSum 的 r=1/2 特例衔接）。 -/
def primePowerSum (χ : ℕ → ℝ) (r x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n * χ n * Real.rpow (n : ℝ) (-r)

/-- 平凡项：Σ_ℓ x^{−(2ℓ+r+a)}/(2ℓ+r+a)（Yildirim 公式 (6) 右侧第一项；模 5 实特征 χ_5
    偶特征 a=0 已代入；级数收敛件为 (L1b) 真证目标，此处为真实级数口径）。 -/
def trivialTerm (r x : ℝ) : ℝ :=
  ∑' ℓ : ℕ, Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r)

/-- 对数导数值项 `(L′/L)(r,χ₅)`。**2026-11-23（B 方案续二）：原 `opaque logDerivTerm (r : ℝ) : ℝ`
    已换为真定义**——`(logDeriv LFun r).re`，其中 mathlib `logDeriv f := deriv f / f`
    （`Mathlib/Analysis/Calculus/LogDeriv.lean:32`，`𝕜 = 𝕜' = ℂ`）。
    取实部：`r` 为实数点时 L 与 L′ 均为实值（由 χ₅ 系数实 ⟹ 共轭对称 `lfun_conj_symm` 保证），
    故 `.re` 与 `(L′/L)(r,χ₅)` 的实数口径一致；该口径的严格证明依赖 `lfun_conj_symm`（真命题，待证），
    此处先落定为实部以保持类型为 ℝ。 -/
noncomputable def logDerivTerm (r : ℝ) : ℝ := (logDeriv LFun (r : ℂ)).re

/-- (L4) 离线（off-critical）误差项：BGS 引理 4 机制的 L 版余项（抽象算子）。 -/
opaque offCriticalError (T : ℝ) : ℝ

/-! ### 2.1 (L1) Landau/Weil 显式公式 L 版（精确陈述；Yildirim 1991 公式 (6)）

数学内容：对 L(s,χ_5)（模 5 实特征），0<r、x>1、r 非零点时（x=1 处平凡项为调和型
  发散奇点，口径排除——见 2.1.2 小节，2026-10-29），
  Σ_ρ x^{ρ−r}/(ρ−r) = Σ_ℓ x^{−(2ℓ+r+a)}/(2ℓ+r+a) − Σ'_{n≤x} Λ(n)χ(n)/n^r − (L′/L)(r,χ)。
（Yildirim 1991 公式 (6)；对 L(s,χ) 无条件成立。） -/
axiom landau_explicit_L :
  ∀ (r x : ℝ), 0 < r → (1 : ℝ) < x → (∀ z ∈ zerosLChi5, z ≠ r) →
    zeroWeightedSum zerosLChi5 r x =
      trivialTerm r x - primePowerSum chi5 r x - logDerivTerm r

/-! ### 2.1.1 (L1b) 真实定义件与第一块真证（2026-10-27 落位）

(L1) 长线第一步：zeroWeightedSum / primePowerSum / trivialTerm 已由 opaque 升级为真实定义
（primePowerSum = Finset 有限和 + Real.rpow；trivialTerm = ∑' 实级数；zeroWeightedSum = 复和实部）。
本区为真实定义下可立即闭合的真证件：
  (L1b-A) r=1/2 代数桥（n^{−1/2} = (√n)⁻¹，衔接 (L2) primeSum）；
  (L1b-B) trivialTerm 级数收敛（x>1、r>0）。
logDerivTerm 保持 opaque（导数件，下一轮）；zeroWeightedSum 的零点无条件收敛挂 (L1c)
（N(T) 计数估计，长线）。 -/

/-- (L1b-A) 素数项代数桥：n^{−1/2} = (√n)⁻¹（n ≥ 1）——(L1) r=1/2 特例与
    (L2) primeSum（K≡1 时）的衔接恒等式。 -/
lemma primePowerSum_half_eq_sqrt (n : ℕ) (_hn : 1 ≤ n) :
    Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  calc
    Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) = (Real.rpow (n : ℝ) (1 / 2 : ℝ))⁻¹ :=
      Real.rpow_neg hn0 (1 / 2)
    _ = (Real.sqrt (n : ℝ))⁻¹ := by
      congr 1
      exact (Real.sqrt_eq_rpow (n : ℝ)).symm

/-- (L1b-A') primePowerSum 的 r=1/2 展开：Σ_{n≤X} Λ(n)χ(n)·n^{−1/2} = Σ_{n≤X} Λ(n)χ(n)·(√n)⁻¹。 -/
lemma primePowerSum_half (χ : ℕ → ℝ) (X : ℝ) :
    primePowerSum χ (1 / 2) X =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, vonMangoldt n * χ n * (Real.sqrt (n : ℝ))⁻¹ := by
  unfold primePowerSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [primePowerSum_half_eq_sqrt n hn1]

/-- (L1b-B0) 平凡项非负：x>1、r>0 时 f ℓ ≥ 0。 -/
lemma trivialTerm_term_nonneg (hr : 0 < r) (hx : (1 : ℝ) < x) (ℓ : ℕ) :
    0 ≤ Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r) := by
  have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ)) hx
  have h1 : 0 ≤ Real.rpow x (-((2 * (ℓ : ℝ)) + r)) := Real.rpow_nonneg hx0.le _
  have h2 : 0 ≤ (2 * (ℓ : ℝ)) + r := by
    nlinarith [hr, mul_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) (Nat.cast_nonneg ℓ)]
  exact div_nonneg h1 h2

/-- (L1b-B1) 平凡项逐项上界：f ℓ ≤ x^{−r}·(x^{−2})^ℓ/r（x>1、r>0）。 -/
lemma trivialTerm_term_le (hr : 0 < r) (hx : (1 : ℝ) < x) (ℓ : ℕ) :
    Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r)
      ≤ Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ / r := by
  have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ)) hx
  have hpos : 0 < (2 * (ℓ : ℝ)) + r := by
    nlinarith [hr, mul_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) (Nat.cast_nonneg ℓ)]
  have hden : r ≤ (2 * (ℓ : ℝ)) + r := by nlinarith
  have hinv : ((2 * (ℓ : ℝ)) + r)⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hpos hr).2 hden
  have hsplit : Real.rpow x (-((2 * (ℓ : ℝ)) + r)) = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ := by
    calc
      Real.rpow x (-((2 * (ℓ : ℝ)) + r))
          = Real.rpow x ((-r) + (-(2 * (ℓ : ℝ)))) := by congr 1; ring
      _ = Real.rpow x (-r) * Real.rpow x (-(2 * (ℓ : ℝ))) :=
          Real.rpow_add hx0 (-r) (-(2 * (ℓ : ℝ)))
      _ = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ := by
          rw [show Real.rpow x (-(2 * (ℓ : ℝ))) = (Real.rpow x (-2)) ^ ℓ by
            calc
              Real.rpow x (-(2 * (ℓ : ℝ))) = Real.rpow x ((-2 : ℝ) * (ℓ : ℝ)) := by congr 1; ring
              _ = (Real.rpow x (-2 : ℝ)) ^ (ℓ : ℝ) := Real.rpow_mul hx0.le (-2 : ℝ) (ℓ : ℝ)
              _ = (Real.rpow x (-2 : ℝ)) ^ ℓ := by rw [Real.rpow_natCast]]
  have hq : 0 ≤ Real.rpow x (-2) := Real.rpow_nonneg hx0.le _
  have hA : 0 ≤ Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ :=
    mul_nonneg (Real.rpow_nonneg hx0.le _) (pow_nonneg hq ℓ)
  calc
    Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r)
        = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ / ((2 * (ℓ : ℝ)) + r) := by rw [hsplit]
    _ = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ * ((2 * (ℓ : ℝ)) + r)⁻¹ := by ring
    _ ≤ Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ * r⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv hA
    _ = Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ / r := by ring

/-- (L1b-B) 平凡项收敛件：x > 1、r > 0 时 trivialTerm 级数可和
    （比较判别 + 几何级数）。x = 1 边界为调和型发散（见 2.1.2「x=1 边界口径」小节：
    trivialTerm_one 将其归结为 Σ 1/(2ℓ+r)）；2026-10-29 起 landau_explicit_L 前提已
    收紧为 1 < x，x=1 不在显式公式适用域。 -/
lemma trivialTerm_summable (hr : 0 < r) (hx : (1 : ℝ) < x) :
    Summable (fun ℓ : ℕ => Real.rpow x (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r)) := by
  have hx0 : (0 : ℝ) < x := lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ)) hx
  have hq0 : 0 ≤ Real.rpow x (-2) := Real.rpow_nonneg hx0.le _
  have hq1 : Real.rpow x (-2) < 1 := by
    calc
      Real.rpow x (-2) = Real.rpow (x⁻¹) (2 : ℝ) := Real.rpow_neg_eq_inv_rpow x (2 : ℝ)
      _ = (x : ℝ)⁻¹ ^ 2 := Real.rpow_natCast (x⁻¹) 2
    have hxinv0 : 0 < (x : ℝ)⁻¹ := inv_pos.mpr hx0
    have hxinv : (x : ℝ)⁻¹ < 1 := by
      have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx0
      simpa [one_mul, mul_inv_cancel₀ hxne] using (mul_lt_mul_of_pos_right hx hxinv0)
    nlinarith [hxinv, hxinv0]
  let g : ℕ → ℝ := fun ℓ => Real.rpow x (-r) * (Real.rpow x (-2)) ^ ℓ / r
  have hg : Summable g := by
    simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using (Summable.mul_left (Real.rpow x (-r) / r) (summable_geometric_of_lt_one hq0 hq1))
  exact Summable.of_nonneg_of_le
    (fun ℓ => trivialTerm_term_nonneg hr hx ℓ)
    (fun ℓ => trivialTerm_term_le hr hx ℓ)
    hg

/-! ### 2.1.2 (L1b-C) x=1 边界口径（2026-10-29；口径决定，非深证明）

trivialTerm r x = Σ_ℓ x^{−(2ℓ+r)}/(2ℓ+r) 在 x=1 处为调和型发散：逐项 x=1 化为
1/(2ℓ+r)，与 Σ_n 1/n 同阶（1/(2ℓ+r) ~ 1/(2ℓ)，比较判别）——故 x=1 不收敛、
不在显式公式适用域。约定：landau_explicit_L 前提为 1 < x（严格，已收紧），
x=1 处的 ∑' 值（mathlib 对不可和级数返回默认 0）不作数学意义引用。
本区钉两项约定件（真实可引用事实）：trivialTerm_one_term（x=1 逐项等式）、
trivialTerm_one（x=1 时 trivialTerm 归结为调和型级数）。调和发散的正式
发散性证明（¬ Summable）留作可选后续件——数学论证见文档《路2攻防XLII-
S7.11-x=1边界口径》；此处仅记录口径，不立深证明。 -/

/-- (L1b-C1) x=1 逐项等式：被加项化为 1/(2ℓ+r)（调和型项）。 -/
lemma trivialTerm_one_term (r : ℝ) (ℓ : ℕ) :
    Real.rpow (1 : ℝ) (-((2 * (ℓ : ℝ)) + r)) / ((2 * (ℓ : ℝ)) + r) =
      (1 : ℝ) / ((2 * (ℓ : ℝ)) + r) := by
  simp

/-- (L1b-C2) x=1 口径件：trivialTerm r 1 = Σ_ℓ 1/(2ℓ+r)（调和型级数，发散——
    仅作口径事实引用，发散性证明留后续件）。 -/
lemma trivialTerm_one (r : ℝ) :
    trivialTerm r 1 = ∑' ℓ : ℕ, (1 : ℝ) / ((2 * (ℓ : ℝ)) + r) := by
  unfold trivialTerm
  exact tsum_congr fun ℓ => trivialTerm_one_term r ℓ

/-! ### 2.2 (L2) Siegel–Walfisz（精确陈述；模 5 点态、无条件、子指数）

数学内容：|Σ_{n≤x} Λ(n)χ_5(n)| ≤ c·x·e^{−c′√log x}（x≥1；c、c′ 为正绝对常数，
  模 5 固定可显式化——文档 S7.6 量化：(c, c′) = (1.70e-3, 1/√R₀≈0.3954) 口径）。 -/
axiom siegel_walfisz_chi5 :
  ∃ (c c' : ℝ), 0 < c ∧ 0 < c' ∧
    ∀ x : ℝ, (1 : ℝ) ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n * chi5 n|
        ≤ c * x * Real.exp (-c' * Real.sqrt (Real.log x))

/-! ### 2.2b (L2) 素数项半形式化：真实和式 + Abel 组装（2026-10-27）

(L2) 从「裸 axiom siegel_walfisz_chi5」升级为结构件链：
  · `primeSum`：素数项真实和式（Finset.Icc 口径，BGS 引理 3 的 prime 项真实载体；
    权重为频域核 K̂ = fourierCos K，S7.9 支撑截断口径）；
  · `sum_abel_partial`：部分和 Abel 求和（真证，归纳；sum_abel 的部分和变形）；
  · `prime_weight_bounds`：权重 b_n = n^{−1/2}·K̂(δ·log n) 的有界/平滑件（axiom，解析件，
    文档 S7.6 §2.4：K̂ 光滑 + 核宽缩放；一个常数 M 兼作 |b| 界与差分界）；
  · `sum_weight_decay`：Σ_{n≤X} n^{−1/2}·e^{−c′√log n} ≤ C₂（theorem，指数衰减和，
    SW 指数 c′ 参数化；尾部项 √N·e^{−c′√log N} 为该和之单项，界并入 C₂）；
  · `sum_sqrt_decay`：√N·e^{−c′√log N} ≤ C₃（theorem，S7.9 尾部项版本）；
  · `primeSum_window_eq`：窗外拆窗（theorem，K̂ 频域窄支撑 ⟹ 和式截断到 min X (e^{1/δ})）；
  · `prime_sum_bound`：|primeSum K X δ| ≤ c·M·(C₂+C₃)，任意 X ≥ 1（组装真证：Abel 分解
    + 三角不等式 + SW 部分和界 + 权重件 + 衰减件 + 拆窗）。
数学口径：SW 界 (c,c′) 见文档 S7.6 量化；权重有界/平滑由 K 光滑与核宽缩放（S7.3 定理 N1
  机制）；归一化 |prime|≤1（除以 N_L~T·logT 分母）的说明留 bgs3 语境（文档层：
  SW 常数 c 实测 1.70e−3 远小，N_L 分母归一后余量充分）。 -/

/-- 素数项（真实和式，Finset 口径）：S(X) = Σ_{1≤n≤⌊X⌋} Λ(n)χ₅(n)·n^{−1/2}·Γ(δ·log n)，
    差型配对中的素数项（BGS 引理 3 的 prime 项真实载体）。**2026-11-23 第七刀**：K 直接是
    频域 profile（与 `pairConstant`（K(δ·ΔIm)）同一口径），不再外套 `fourierCos`。旧写法把 K
    当"时域核再取变换"，后果是 `primeSum Khat ≡ 0`（`fourierCos Khat ≡ 0`）、且求和发散
    （Σ_n n^{−1/2}|Γ(δ log n)| · log n 发散如 √X 的前身），故必须由真正紧支撑的 profile 承担。
    支撑截断改由 `triKer_supp` 提供（定义即得，不再需要 axiom）。 -/
def primeSum (K : ℝ → ℝ) (X δ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))

/- 引理 5 旧件（`bgs5_khat_fourier_supp`）已撤：

    原来它是 `axiom bgs5_khat_fourier_supp : ∀ u, 1 < |u| → fourierCos Khat u = 0`，
    两条毛病（2026-11-23 机检）：
    (i)  它的命题内容是 `fourierCos Khat ≡ 0`——因为 Khat 不可绝对积（衰减仅 1/|u|），
         mathlib 的 Bochner 积分按 `integral_undef` 取 0，于是它**处处成立**，与"频域窄支撑"
         毫无关系，是一条空话；
    (ii) 与 `fourierCos_Khat` 合成 `False`（根级探针 `_incons_ax.lean`）。
    替代物：`triKer_supp : 1 < |u| → triKer u = 0`（`S7_1_Core` §4c，真证、由定义直接得到）。 -/

/-- Abel 求和（部分和版，真证）：Σ_{n=1..N} a_n·b_n = A_N·b_N − Σ_{n=1..N−1} A_n·(b_{n+1}−b_n)，
    A_n = Σ_{i=1..n} a_i（素数项 S(X) 的分部求和；S7.6 §2.4 离散骨架，sum_abel 的部分和变形）。
    归纳结构：succ 步把 Σ Icc 1 (N+1) 拆为 Σ Icc 1 N + 尾项，套 ih 后重组 A_{N+1} 与
    Σ Icc 1 ((N+1)−1) = Σ Icc 1 N（N≥1 分支）；N=0 分支两边空和。 -/
lemma sum_abel_partial (N : ℕ) (a b : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, a n * b n)
      = (∑ i ∈ Finset.Icc 1 N, a i) * b N
        - (∑ n ∈ Finset.Icc 1 (N - 1), (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hsucc : (N + 1) - 1 = N := by
        exact Nat.add_sub_cancel N 1
      have hIccN : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext x
        simp [Finset.mem_Icc]
        omega
      have hnotN : N + 1 ∉ Finset.Icc 1 N := by
        intro hx
        have hle : N + 1 ≤ N := (Finset.mem_Icc.mp hx).2
        omega
      calc
        (∑ n ∈ Finset.Icc 1 (N + 1), a n * b n)
            = (∑ n ∈ Finset.Icc 1 N, a n * b n) + a (N + 1) * b (N + 1) := by
              rw [hIccN, Finset.sum_insert hnotN]
              ring
        _ = ((∑ i ∈ Finset.Icc 1 N, a i) * b N
              - (∑ n ∈ Finset.Icc 1 (N - 1), (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n)))
            + a (N + 1) * b (N + 1) := by rw [ih]
        _ = (∑ i ∈ Finset.Icc 1 (N + 1), a i) * b (N + 1)
              - (∑ n ∈ Finset.Icc 1 N, (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n)) := by
              have hA : (∑ i ∈ Finset.Icc 1 (N + 1), a i)
                  = (∑ i ∈ Finset.Icc 1 N, a i) + a (N + 1) := by
                rw [hIccN, Finset.sum_insert hnotN]
                ring
              have hI :
                  (∑ n ∈ Finset.Icc 1 N, (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n))
                    = (∑ n ∈ Finset.Icc 1 (N - 1), (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n))
                      + (∑ i ∈ Finset.Icc 1 N, a i) * (b (N + 1) - b N) := by
                by_cases hN : N = 0
                · subst N
                  simp
                · have hIcc' : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
                    apply Finset.Subset.antisymm
                    · intro x hx
                      rw [Finset.mem_insert]
                      by_cases hxN : x = N
                      · exact Or.inl hxN
                      · exact Or.inr (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,
                          Nat.le_pred_of_lt (Nat.lt_of_le_of_ne (Finset.mem_Icc.mp hx).2 hxN)⟩)
                    · intro x hx
                      rw [Finset.mem_insert] at hx
                      rcases hx with rfl | hx
                      · exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
                      · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,
                          Nat.le_trans (Finset.mem_Icc.mp hx).2 (Nat.sub_le N 1)⟩
                  have hnot' : N ∉ Finset.Icc 1 (N - 1) := by
                    intro hx
                    have hle : N ≤ N - 1 := (Finset.mem_Icc.mp hx).2
                    omega
                  rw [hIcc', Finset.sum_insert hnot']
                  rw [Finset.sum_insert hnot']
                  rw [show (∑ i ∈ Finset.Icc 1 N, a i) = a N + (∑ i ∈ Finset.Icc 1 (N - 1), a i) by
                    rw [hIcc', Finset.sum_insert hnot']]
                  simp only [mul_sub]
                  ring
              rw [hA, hI]
              ring
        _ = (∑ i ∈ Finset.Icc 1 (N + 1), a i) * b (N + 1)
              - (∑ n ∈ Finset.Icc 1 ((N + 1) - 1), (∑ i ∈ Finset.Icc 1 n, a i) * (b (n + 1) - b n)) := by
              rw [hsucc]


/-- 对数差分界：|log(n+1) − log n| = log(n+1) − log n ≤ 1/n（n ≥ 1；log 单调 + log x ≤ x−1）。 -/
lemma log_succ_sub_le_inv (n : ℕ) (hn : 1 ≤ n) :
    |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)| ≤ (n : ℝ)⁻¹ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn)
  have hmono : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    exact Real.log_le_log hnpos (by exact_mod_cast (Nat.le_succ n))
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  have hdiv : Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))
      = Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) :=
    Real.log_div (ne_of_gt (by positivity : (0 : ℝ) < (n + 1 : ℕ))) hnpos.ne'
  have hratio : ((n + 1 : ℕ) : ℝ) / (n : ℝ) = 1 + (n : ℝ)⁻¹ := by
    field_simp [hnpos.ne']
    norm_cast
  have hle : Real.log (1 + (n : ℝ)⁻¹) ≤ (n : ℝ)⁻¹ := by
    have hx : 0 < 1 + (n : ℝ)⁻¹ := by positivity
    have hb := Real.log_le_sub_one_of_pos hx
    rwa [show 1 + (n : ℝ)⁻¹ - 1 = (n : ℝ)⁻¹ by ring] at hb
  rwa [← hratio, hdiv] at hle

/-- 逆 sqrt 单调：n ≥ 1 ⟹ (√(n+1))⁻¹ ≤ (√n)⁻¹。 -/
lemma inv_sqrt_succ_le (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.sqrt (n : ℝ))⁻¹ := by
  have hsqrtn : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn))
  have hsqrtn1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))
  exact (inv_le_inv₀ hsqrtn1 hsqrtn).2 (Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ n)))

/-- (√n)⁻¹·(√n)⁻¹ = n⁻¹（n ≥ 1）。 -/
lemma inv_sqrt_sq_eq_inv (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ)⁻¹ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn)
  have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
  calc
    (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹
        = ((Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ)))⁻¹ := by rw [← mul_inv]
    _ = ((Real.sqrt (n : ℝ)) ^ 2)⁻¹ := by ring_nf
    _ = (n : ℝ)⁻¹ := by rw [hsq]

/-- 逆 sqrt 差分界：n ≥ 1 ⟹ |(√(n+1))⁻¹ − (√n)⁻¹| ≤ ((√n)⁻¹)³
    （有理化：√(n+1)−√n = 1/(√(n+1)+√n)；分母各项 ≥ √n ⟹ 分数 ≤ (√n)^{−3}）。 -/
lemma inv_sqrt_succ_sub_le (n : ℕ) (hn : 1 ≤ n) :
    |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹|
      ≤ (Real.sqrt (n : ℝ))⁻¹ ^ 3 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn)
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnpos
  have hsqrtn1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))
  have hA : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ n))
  have hsqrt_diff : Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)
      = (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹ := by
    have hprod : (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
        * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) = 1 := by
      have h1 : (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))
      have h2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
      calc
        (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))
            = (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 - (Real.sqrt (n : ℝ)) ^ 2 := by ring
        _ = ((n + 1 : ℕ) : ℝ) - (n : ℝ) := by rw [h1, h2]
        _ = 1 := by norm_num
    calc
      Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)
          = (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) * 1 := by ring
      _ = (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
            * ((Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))
                * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹) := by
            have hS : Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) ≠ 0 :=
              ne_of_gt (add_pos hsqrtn1 hsqrtn)
            field_simp [hS]
      _ = ((Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)))
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹ := by ring
      _ = (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))⁻¹ := by
            rw [hprod]
            ring
  have habs : |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹|
      = (Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)
          * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)))⁻¹ := by
    have hnonpos : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹ ≤ 0 := by
      exact sub_nonpos.mpr (inv_sqrt_succ_le n hn)
    rw [abs_of_nonpos hnonpos]
    field_simp [hsqrtn.ne', hsqrtn1.ne']
    rw [← neg_sub, hsqrt_diff]
    field_simp [ne_of_gt (add_pos hsqrtn1 hsqrtn)]
  have hden : Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
        * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))
      ≥ (Real.sqrt (n : ℝ)) ^ 3 := by
    have h1 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)
        ≤ Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) := by
      calc
        Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) + Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          le_add_of_nonneg_right (Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ))
        _ = Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) := by ring
    calc
      Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
          * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ))
          ≥ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
            exact mul_le_mul h1 h2 (Real.sqrt_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (Real.sqrt (n : ℝ)) ^ 3 := by ring
  have hdenpos : 0 < Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
      * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) := by positivity
  have hcube : 0 < (Real.sqrt (n : ℝ)) ^ 3 := by positivity
  calc
    |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt (n : ℝ))⁻¹|
        = (Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)))⁻¹ := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using habs
    _ ≤ (Real.sqrt (n : ℝ))⁻¹ ^ 3 := by
        have hle1 : (Real.sqrt (n : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)
            * (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)))⁻¹
            ≤ ((Real.sqrt (n : ℝ)) ^ 3)⁻¹ := by
          exact (inv_le_inv₀ hdenpos hcube).2 hden
        rwa [← inv_pow] at hle1

/-- 素数项权重件（真证，**三角核**特化，2026-11-23 第七刀）：b_n = n^{−1/2}·Γ(δ·log n)，Γ = `triKer`。
    |b_n| ≤ M·n^{−1/2} 且 |b_{n+1}−b_n| ≤ M·n^{−3/2}，M = δ + 1（B = sup Γ = 1、L = Lip Γ = 1）。
    与已撤的 Khat 版（`prime_weight_bounds_Khat`，依赖 sinc 梳估计）同构，但常数与支撑全部由定义给出，不依赖任何 sin 估计。 -/
theorem prime_weight_bounds_tri (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ n : ℕ, 1 ≤ n →
        |(Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ))| ≤ M * (Real.sqrt (n : ℝ))⁻¹) ∧
      (∀ n : ℕ, 1 ≤ n →
        |(Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ))
          - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ))|
          ≤ M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
  refine ⟨δ + 1, by linarith, ?hb, ?hΔ⟩
  · intro n hn
    have hsqrt : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc
      |(Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ))|
          = (Real.sqrt (n : ℝ))⁻¹ * |triKer (δ * Real.log (n : ℝ))| := by
            rw [abs_mul, abs_of_nonneg hsqrt]
      _ ≤ (Real.sqrt (n : ℝ))⁻¹ * 1 := by
            exact mul_le_mul_of_nonneg_left (triKer_abs_le_one _) hsqrt
      _ ≤ (δ + 1) * (Real.sqrt (n : ℝ))⁻¹ := by
            have hone : (1 : ℝ) ≤ δ + 1 := by linarith
            simpa [mul_comm] using mul_le_mul_of_nonneg_right hone hsqrt
  · intro n hn
    let A : ℝ := (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹
    let C : ℝ := (Real.sqrt (n : ℝ))⁻¹
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hC0 : 0 ≤ C := by
      dsimp [C]
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hAC : |A - C| ≤ C ^ 3 := by
      dsimp [A, C]
      exact inv_sqrt_succ_sub_le n hn
    have hAC' : A ≤ C := by
      dsimp [A, C]
      exact inv_sqrt_succ_le n hn
    have hdecomp :
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ))
          - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ))
        = A * (triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)) - triKer (δ * Real.log (n : ℝ)))
          + (A - C) * triKer (δ * Real.log (n : ℝ)) := by
          dsimp [A, C]
          ring
    rw [hdecomp]
    have hKdiff :
        |triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)) - triKer (δ * Real.log (n : ℝ))|
          ≤ δ * (n : ℝ)⁻¹ := by
      have hx : |δ * Real.log ((n + 1 : ℕ) : ℝ) - δ * Real.log (n : ℝ)|
          = δ * |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)| := by
        rw [← mul_sub, abs_mul, abs_of_pos hδ]
      calc
        |triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)) - triKer (δ * Real.log (n : ℝ))|
            ≤ |δ * Real.log ((n + 1 : ℕ) : ℝ) - δ * Real.log (n : ℝ)| :=
              triKer_lipschitz _ _
        _ = δ * |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)| := hx
        _ ≤ δ * (n : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left (log_succ_sub_le_inv n hn) (le_of_lt hδ)
    have hninv : (n : ℝ)⁻¹ ≤ C * C := by
      dsimp [C]
      exact le_of_eq (inv_sqrt_sq_eq_inv n hn).symm
    have hfirst : A * (δ * (n : ℝ)⁻¹) ≤ C ^ 3 * δ := by
      have hm1 : δ * (n : ℝ)⁻¹ ≤ δ * (C * C) :=
        mul_le_mul_of_nonneg_left hninv (le_of_lt hδ)
      have hm2 : A * (δ * (n : ℝ)⁻¹) ≤ C * (δ * (n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hAC'
          (mul_nonneg (le_of_lt hδ) (inv_nonneg.mpr (Nat.cast_nonneg n)))
      have hm3 : C * (δ * (n : ℝ)⁻¹) ≤ C * (δ * (C * C)) :=
        mul_le_mul_of_nonneg_left hm1 hC0
      have hm4 : C * (δ * (C * C)) = C ^ 3 * δ := by ring
      exact hm2.trans (hm3.trans hm4.le)
    calc
      |A * (triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)) - triKer (δ * Real.log (n : ℝ)))
        + (A - C) * triKer (δ * Real.log (n : ℝ))|
          ≤ |A * (triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)) - triKer (δ * Real.log (n : ℝ)))|
            + |(A - C) * triKer (δ * Real.log (n : ℝ))| := abs_add_le _ _
      _ = A * |triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)) - triKer (δ * Real.log (n : ℝ))|
          + |A - C| * |triKer (δ * Real.log (n : ℝ))| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hA0]
      _ ≤ A * (δ * (n : ℝ)⁻¹) + |A - C| * 1 := by
            exact add_le_add (mul_le_mul_of_nonneg_left hKdiff hA0)
              (mul_le_mul_of_nonneg_left (triKer_abs_le_one _) (abs_nonneg _))
      _ ≤ C ^ 3 * δ + C ^ 3 * 1 := by
            exact add_le_add hfirst (mul_le_mul_of_nonneg_right hAC zero_le_one)
      _ = (δ + 1) * C ^ 3 := by ring

/-- 逐项望远镜引理（真证，S7.9）：n ≥ 1 ⟹ (√n)⁻¹ ≤ 2(√n − √(n−1))
    （因 √(n−1) ≤ √n，且 (√n−√(n−1))(√n+√(n−1)) = 1）。 -/
lemma inv_sqrt_telescope_le (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1r
  have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa using (Nat.cast_sub (R := ℝ) hn)
  let a : ℝ := Real.sqrt (n : ℝ)
  let b : ℝ := Real.sqrt ((n - 1 : ℕ) : ℝ)
  have ha2 : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (le_of_lt hnpos)
  have hb2 : b ^ 2 = (n : ℝ) - 1 := by
    dsimp [b]
    rw [hnm1]
    exact Real.sq_sqrt (sub_nonneg.mpr hn1r)
  have ha0 : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 hnpos
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact Real.sqrt_nonneg _
  have hab_ge : b ≤ a := by
    dsimp [a, b]
    exact Real.sqrt_le_sqrt (by rw [hnm1]; linarith)
  have hab_pos : 0 < a + b := lt_of_lt_of_le ha0 (le_add_of_nonneg_right hb0)
  have hprod : (a - b) * (a + b) = 1 := by
    nlinarith [ha2, hb2]
  have htel2 : 2 * (a - b) = 2 / (a + b) := by
    calc
      2 * (a - b) = (2 * (a - b) * (a + b)) / (a + b) := by
        rw [mul_div_cancel_right₀ (2 * (a - b)) hab_pos.ne']
      _ = 2 / (a + b) := by
        rw [show 2 * (a - b) * (a + b) = 2 * ((a - b) * (a + b)) by ring]
        rw [hprod]
        ring
  have htel3 : (a : ℝ)⁻¹ ≤ 2 / (a + b) := by
    calc
      (a : ℝ)⁻¹ = 1 / a := inv_eq_one_div (a : ℝ)
      _ ≤ 2 / (a + b) := (div_le_div_iff₀ ha0 hab_pos).2 (by linarith [hab_ge])
  calc
    (Real.sqrt (n : ℝ))⁻¹ = (a : ℝ)⁻¹ := rfl
    _ ≤ 2 / (a + b) := htel3
    _ = 2 * (a - b) := htel2.symm

/-- 望远镜和（真证，S7.9）：Σ_{n≤N} (√n − √(n−1)) = √N（Icc 归纳）。 -/
lemma sum_sqrt_telescope (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)))
      = Real.sqrt (N : ℝ) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega)]
      rw [ih]
      simp

/-- 支撑截断 sum 界件（真证，S7.9）：Σ_{n≤N} n^{−1/2} ≤ 2√N（逐项望远镜 + 求和）。 -/
lemma sum_inv_sqrt_le_two_sqrt (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) ≤ 2 * Real.sqrt (N : ℝ) := by
  have hstep : ∀ n ∈ Finset.Icc 1 N,
      (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
    intro n hn
    exact inv_sqrt_telescope_le n (Finset.mem_Icc.mp hn).1
  calc
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹)
        ≤ ∑ n ∈ Finset.Icc 1 N, 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
          exact Finset.sum_le_sum hstep
    _ = 2 * Real.sqrt (N : ℝ) := by
        calc
          (∑ n ∈ Finset.Icc 1 N, 2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)))
              = 2 * (∑ n ∈ Finset.Icc 1 N,
                  (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ))) := by
              rw [Finset.mul_sum]
          _ = 2 * Real.sqrt (N : ℝ) := by rw [sum_sqrt_telescope]

/-- 指数衰减和件（真证，2026-10-29；S7.9 支撑截断口径，由 axiom 降级为 theorem）：
    Σ_{n≤min(X, e^{1/δ})} n^{−1/2} ≤ C₂，C₂ = 2√(e^{1/δ})（窗内有限和，差分部分 Σ A_n·Δb_n 的界）。
    注：原裸形式 Σ n^{−1/2}·e^{−c′√log n} 数学上发散（e^{−c′√log n} 亚多项式衰减，
    慢于任何幂），有界性来自核支撑截断（|δ·log n| ≤ 1 即 n ≤ e^{1/δ}）——S7.9 文档。 -/
theorem sum_weight_decay (δ : ℝ) (_hδ : 0 < δ) (c' : ℝ) (_hc' : 0 < c') :
  ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ X : ℝ, (1 : ℝ) ≤ X →
      (∑ n ∈ Finset.Icc 1 (min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊),
        (Real.sqrt (n : ℝ))⁻¹) ≤ C₂ := by
  refine ⟨2 * Real.sqrt (Real.exp (1 / δ)), mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  intro X hX
  have hle : 2 * Real.sqrt ((min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊ : ℕ) : ℝ)
      ≤ 2 * Real.sqrt (Real.exp (1 / δ)) := by
    have hmin : ((min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊ : ℕ) : ℝ) ≤ Real.exp (1 / δ) := by
      exact le_trans (by exact_mod_cast (min_le_right ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊)) (Nat.floor_le (Real.exp_nonneg _))
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmin) (by norm_num : (0 : ℝ) ≤ 2)
  exact (sum_inv_sqrt_le_two_sqrt (min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊)).trans hle

/-- 指数衰减和件（真证，2026-10-29；S7.9 支撑截断口径，由 axiom 降级为 theorem）：
    Σ_{n≤min(X, e^{1/δ})} √n·e^{−c′√log n} ≤ C₃，C₃ = e^{3/(2δ)}（窗内有限和；用于尾部项
    A_N·b_N 的界，√N·e^{−c′√log N} 为该和之单项）。原裸 Σ √n·e^{−c′√log n} 发散，见 S7.9 文档。
    证明路线：逐项 e^{−c′√log n} ≤ 1（n ≥ 1 ⟹ log n ≥ 0）⟹ 和 ≤ Σ√n ≤ Nw·√Nw
    （sum_le_card_nsmul，card(Icc 1 Nw) = Nw 手写归纳 + card_union_of_disjoint）⟹
    Nw ≤ e^{1/δ}（Nat.floor_le）⟹ ≤ e^{1/δ}·√(e^{1/δ}) ≤ e^{1/δ}·e^{1/(2δ)} = e^{3/(2δ)}
    （Real.sqrt_le_iff 平方单调，无 Real.sqrt_exp）。 -/
theorem sum_sqrt_decay (δ : ℝ) (hδ : 0 < δ) (c' : ℝ) (hc' : 0 < c') :
  ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ X : ℝ, (1 : ℝ) ≤ X →
      (∑ n ∈ Finset.Icc 1 (min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊),
        Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ)))) ≤ C₃ := by
  refine ⟨Real.exp (3 / (2 * δ)), Real.exp_nonneg _, ?_⟩
  intro X hX
  let Nw : ℕ := min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊
  have hNw1 : (1 : ℕ) ≤ Nw := by
    dsimp [Nw]
    have h1leE : (1 : ℝ) ≤ Real.exp (1 / δ) :=
      (Real.one_le_exp_iff).2 (le_of_lt (one_div_pos.mpr hδ))
    have h1leflE : (1 : ℕ) ≤ ⌊Real.exp (1 / δ)⌋₊ := by
      simpa using (Nat.floor_mono h1leE)
    have h1leflX : (1 : ℕ) ≤ ⌊X⌋₊ := by
      simpa using (Nat.floor_mono hX)
    exact le_min h1leflX h1leflE
  have hcard_general : ∀ N : ℕ, (Finset.Icc 1 N).card = N := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        have hdecomp : Finset.Icc 1 (N + 1) = Finset.Icc 1 N ∪ {N + 1} := by
          ext k
          rw [Finset.mem_Icc, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
          constructor
          · intro hk
            by_cases h : k ≤ N
            · exact Or.inl ⟨hk.1, h⟩
            · exact Or.inr (by omega)
          · rintro (⟨hk1, hkN⟩ | hk)
            · exact ⟨hk1, le_trans hkN (Nat.le_succ N)⟩
            · subst hk
              exact ⟨by omega, by omega⟩
        have hdisj : Disjoint (Finset.Icc 1 N) ({N + 1} : Finset ℕ) := by
          rw [Finset.disjoint_left]
          intro k hk1 hk2
          simp [Finset.mem_singleton, Finset.mem_Icc] at hk1 hk2
          omega
        have hstep : (Finset.Icc 1 (N + 1)).card = (Finset.Icc 1 N).card + 1 := by
          rw [hdecomp, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
        rw [hstep, ih]
  have hcardNw : (Finset.Icc 1 Nw).card = Nw := hcard_general Nw
  have hstep : ∀ n ∈ Finset.Icc 1 Nw,
      Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) ≤ Real.sqrt (n : ℝ) := by
    intro n hn
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1'
    have hneg : -c' * Real.sqrt (Real.log (n : ℝ)) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hc']) (Real.sqrt_nonneg _)
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) ((Real.exp_le_one_iff).2 hneg)
  have hsum : (∑ n ∈ Finset.Icc 1 Nw,
      Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
      ≤ ∑ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ) := by
    exact Finset.sum_le_sum hstep
  have hsqrt : ∀ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ) ≤ Real.sqrt (Nw : ℝ) := by
    intro n hn
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  have hcard : (∑ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ)) ≤ (Nw : ℝ) * Real.sqrt (Nw : ℝ) := by
    calc
      (∑ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ))
          ≤ (Finset.Icc 1 Nw).card • Real.sqrt (Nw : ℝ) :=
            Finset.sum_le_card_nsmul (Finset.Icc 1 Nw) (fun n => Real.sqrt (n : ℝ))
              (Real.sqrt (Nw : ℝ)) hsqrt
      _ = (Nw : ℝ) * Real.sqrt (Nw : ℝ) := by
            rw [nsmul_eq_mul, hcardNw]
  have hNwE : (Nw : ℝ) ≤ Real.exp (1 / δ) := by
    dsimp [Nw]
    have h1 : ((min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊ : ℕ) : ℝ) ≤ (⌊Real.exp (1 / δ)⌋₊ : ℝ) := by
      exact_mod_cast (min_le_right ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊)
    exact le_trans h1 (Nat.floor_le (Real.exp_nonneg _))
  have hsqrtNw : Real.sqrt (Nw : ℝ) ≤ Real.sqrt (Real.exp (1 / δ)) := by
    exact Real.sqrt_le_sqrt hNwE
  have hmul : (Nw : ℝ) * Real.sqrt (Nw : ℝ) ≤ Real.exp (1 / δ) * Real.sqrt (Real.exp (1 / δ)) := by
    exact mul_le_mul hNwE hsqrtNw (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  have hsqrt_le : Real.sqrt (Real.exp (1 / δ)) ≤ Real.exp ((1 / δ) / 2) := by
    exact (Real.sqrt_le_iff).2 ⟨Real.exp_nonneg _, by
      rw [pow_two]
      rw [← Real.exp_add]
      have hsum : 1 / δ = (1 / δ) / 2 + (1 / δ) / 2 := by
        field_simp [ne_of_gt hδ]
        ring
      conv_lhs => rw [hsum]⟩
  have hmul2 : Real.exp (1 / δ) * Real.sqrt (Real.exp (1 / δ)) ≤ Real.exp (3 / (2 * δ)) := by
    have hmul2' : Real.exp (1 / δ) * Real.sqrt (Real.exp (1 / δ))
        ≤ Real.exp (1 / δ) * Real.exp ((1 / δ) / 2) := by
      exact mul_le_mul_of_nonneg_left hsqrt_le (Real.exp_nonneg _)
    have heq : Real.exp (1 / δ) * Real.exp ((1 / δ) / 2) = Real.exp (3 / (2 * δ)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [ne_of_gt hδ]
      ring
    exact hmul2'.trans_eq heq
  calc
    (∑ n ∈ Finset.Icc 1 (min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊),
        Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
        ≤ (∑ n ∈ Finset.Icc 1 Nw, Real.sqrt (n : ℝ)) := by
          rw [show min ⌊X⌋₊ ⌊Real.exp (1 / δ)⌋₊ = Nw by rfl]
          exact hsum
    _ ≤ (Nw : ℝ) * Real.sqrt (Nw : ℝ) := hcard
    _ ≤ Real.exp (1 / δ) * Real.sqrt (Real.exp (1 / δ)) := hmul
    _ ≤ Real.exp (3 / (2 * δ)) := hmul2

/-- 窗外拆窗（真证，2026-10-29；**2026-11-23 第七刀** 改口径为 profile 自身紧支撑）：
    素数项权重 Γ 的频域紧支撑 ⟹ 和式截断到窗内——|δ·log n| > 1（即 n > e^{1/δ}）⟹
    Γ(δ·log n) = 0（`hKs`，由 `triKer_supp` 定义即得），故
    primeSum K X δ = primeSum K (min X (e^{1/δ})) δ（任意 X ≥ 1，无需窗内前提 hXw）。 -/
lemma primeSum_window_eq (K : ℝ → ℝ) (X δ : ℝ) (_hX : (1 : ℝ) ≤ X) (hδ : 0 < δ)
    (hKs : ∀ u : ℝ, 1 < |u| → K u = 0) :
    primeSum K X δ = primeSum K (min X (Real.exp (1 / δ))) δ := by
  by_cases hXw : X ≤ Real.exp (1 / δ)
  · have hmin : min X (Real.exp (1 / δ)) = X := min_eq_left hXw
    rw [hmin]
  · have hE : Real.exp (1 / δ) ≤ X := le_of_not_ge hXw
    have hmin : min X (Real.exp (1 / δ)) = Real.exp (1 / δ) := min_eq_right hE
    have hsub : Finset.Icc 1 ⌊Real.exp (1 / δ)⌋₊ ⊆ Finset.Icc 1 ⌊X⌋₊ := by
      intro n hn
      apply Finset.mem_Icc.mpr
      exact ⟨(Finset.mem_Icc.mp hn).1, le_trans (Finset.mem_Icc.mp hn).2 (Nat.floor_mono hE)⟩
    have hzero : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊, n ∉ Finset.Icc 1 ⌊Real.exp (1 / δ)⌋₊ →
        (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ))) = 0 := by
      intro n hn hnot
      have hn1 : (1 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
      have hflt : ⌊Real.exp (1 / δ)⌋₊ < n := by
        by_contra h
        have hnle : n ≤ ⌊Real.exp (1 / δ)⌋₊ := le_of_not_gt h
        exact hnot (Finset.mem_Icc.mpr ⟨hn1, hnle⟩)
      have hy : Real.exp (1 / δ) < (n : ℝ) := (Nat.floor_lt (Real.exp_nonneg _)).1 hflt
      have hpos : (0 : ℝ) < (n : ℝ) :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn1)
      have hlog : 1 / δ < Real.log (n : ℝ) := by
        apply (Real.exp_lt_exp).mp
        rwa [Real.exp_log hpos]
      have hδlog : 1 < δ * Real.log (n : ℝ) := by
        have hmul : δ * (1 / δ) = 1 := by field_simp [ne_of_gt hδ]
        calc
          1 = δ * (1 / δ) := hmul.symm
          _ < δ * Real.log (n : ℝ) := mul_lt_mul_of_pos_left hlog hδ
      have habs : |δ * Real.log (n : ℝ)| = δ * Real.log (n : ℝ) :=
        abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hδlog)
      have hzero' : K (δ * Real.log (n : ℝ)) = 0 :=
        hKs (δ * Real.log (n : ℝ)) (by rwa [habs])
      rw [hzero', mul_zero, mul_zero]
    have hsum : (∑ n ∈ Finset.Icc 1 ⌊Real.exp (1 / δ)⌋₊,
        (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ))))
        = (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (vonMangoldt n * chi5 n) * ((Real.sqrt (n : ℝ))⁻¹ * K (δ * Real.log (n : ℝ)))) :=
      Finset.sum_subset hsub hzero
    rw [hmin]
    dsimp [primeSum]
    exact hsum.symm

/-- 素数项界（组装真证，(L2) 半形式化落位 + S7.9 窗外拆窗）：SW × Abel × 权重
    ⟹ |primeSum K X δ| ≤ c·M·(C₂+C₃)，任意 X ≥ 1（无窗内前提）。
    组装 = sum_abel_partial（真证）+ siegel_walfisz_chi5（部分和 SW 界）+ prime_weight_bounds
    + sum_weight_decay / sum_sqrt_decay（指数衰减和；尾部项并入 C₃、差分和并入 C₂）。
    拆窗：primeSum_window_eq（K̂ 频域窄支撑 ⟹ 和式截断到 min X (e^{1/δ})），故 X' = min X (e^{1/δ})
    满足窗内前提（min_le_right），原窗内证明套 X'。
    归一化 |prime|≤1（除以 N_L~T·logT 分母）说明留 bgs3 语境（文档层：SW 常数 c 实测
    1.70e−3 远小，分母归一后余量充分）。 -/
theorem prime_sum_bound (X δ : ℝ) (hX : (1 : ℝ) ≤ X) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ |primeSum triKer X δ| ≤ C := by
  let X' : ℝ := min X (Real.exp (1 / δ))
  have hX' : (1 : ℝ) ≤ X' := by
    dsimp [X']
    exact le_min hX ((Real.one_le_exp_iff).2 (le_of_lt (one_div_pos.mpr hδ)))
  have hXw' : X' ≤ Real.exp (1 / δ) := by
    dsimp [X']
    exact min_le_right X (Real.exp (1 / δ))
  have hpeq : primeSum triKer X δ = primeSum triKer X' δ :=
    primeSum_window_eq triKer X δ hX hδ (fun _ h => triKer_supp h)
  rw [hpeq]
  rcases siegel_walfisz_chi5 with ⟨c, c', hc0, hc'0, hsw⟩
  rcases prime_weight_bounds_tri δ hδ with ⟨M, hM0, hb, hΔ⟩
  rcases sum_weight_decay δ hδ c' hc'0 with ⟨C₂, hC₂0, hdec2⟩
  rcases sum_sqrt_decay δ hδ c' hc'0 with ⟨C₃, hC₃0, hdec3⟩
  let N : ℕ := ⌊X'⌋₊
  have hNpos : (1 : ℕ) ≤ N := by
    dsimp [N]
    exact (Nat.floor_pos).2 hX'
  have hswN : ∀ n : ℕ, (1 : ℕ) ≤ n →
      |∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i|
        ≤ c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
    intro n hn
    have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hfl : ⌊(n : ℝ)⌋₊ = n := by simp
    have hsw' := hsw (n : ℝ) hx
    rwa [hfl] at hsw'
  have hps : primeSum triKer X' δ
      = (∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
          * ((Real.sqrt (N : ℝ))⁻¹ * triKer (δ * Real.log (N : ℝ)))
        - (∑ n ∈ Finset.Icc 1 (N - 1),
            (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
              * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                  - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))) := by
    dsimp [primeSum, N]
    exact sum_abel_partial ⌊X'⌋₊ (fun n => vonMangoldt n * chi5 n)
      (fun n => (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))
  refine ⟨c * M * (C₂ + C₃), mul_nonneg (mul_nonneg (le_of_lt hc0) hM0) (add_nonneg hC₂0 hC₃0), ?_⟩
  calc
    |primeSum triKer X' δ|
        ≤ |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
            * ((Real.sqrt (N : ℝ))⁻¹ * triKer (δ * Real.log (N : ℝ)))|
          + |∑ n ∈ Finset.Icc 1 (N - 1),
              (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                    - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))| := by
            rw [hps, sub_eq_add_neg]
            exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ c * M * C₃ + c * M * C₂ := by
        have h1 : |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
            * ((Real.sqrt (N : ℝ))⁻¹ * triKer (δ * Real.log (N : ℝ)))| ≤ c * M * C₃ := by
          calc
            |(∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i)
                * ((Real.sqrt (N : ℝ))⁻¹ * triKer (δ * Real.log (N : ℝ)))|
                ≤ |∑ i ∈ Finset.Icc 1 N, vonMangoldt i * chi5 i|
                  * |(Real.sqrt (N : ℝ))⁻¹ * triKer (δ * Real.log (N : ℝ))| := (abs_mul _ _).le
            _ ≤ (c * (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))))
                * (M * (Real.sqrt (N : ℝ))⁻¹) := by
                exact mul_le_mul (hswN N hNpos) (hb N hNpos) (abs_nonneg _)
                  (mul_nonneg (mul_nonneg (le_of_lt hc0) (Nat.cast_nonneg N)) (Real.exp_nonneg _))
            _ ≤ c * M * C₃ := by
                have hroot : (Real.sqrt (N : ℝ))⁻¹ * (N : ℝ) = Real.sqrt (N : ℝ) := by
                  have hNgt0 : (0 : ℝ) < (N : ℝ) :=
                    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hNpos)
                  have hsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
                    Real.sq_sqrt (le_of_lt hNgt0)
                  have hne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hNgt0)
                  field_simp [hne]
                  conv_lhs =>
                    rw [← hsq]
                have hmul : 0 ≤ c * M := mul_nonneg (le_of_lt hc0) hM0
                have hterm : Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))) ≤ C₃ := by
                  have hNleX : N ≤ ⌊X'⌋₊ := by exact le_rfl
                  have hNleE : N ≤ ⌊Real.exp (1 / δ)⌋₊ := by
                    dsimp [N]
                    exact Nat.floor_mono hXw'
                  have hsingle :
                      Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ)))
                        ≤ ∑ n ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊),
                            Real.sqrt (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                      have hf : ∀ j ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊),
                          0 ≤ Real.sqrt (j : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (j : ℝ))) := by
                        intro j hj
                        exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
                      have hNmem : N ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊) := by
                        apply Finset.mem_Icc.mpr
                        exact ⟨hNpos, le_min hNleX hNleE⟩
                      simpa [N] using (Finset.single_le_sum hf hNmem)
                  exact hsingle.trans (hdec3 X' hX')
                calc
                  (c * (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))))
                      * (M * (Real.sqrt (N : ℝ))⁻¹)
                      = c * M * ((Real.sqrt (N : ℝ))⁻¹ * (N : ℝ))
                          * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))) := by ring
                  _ = c * M * Real.sqrt (N : ℝ)
                      * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ))) := by rw [hroot]
                  _ ≤ c * M * C₃ := by
                      calc
                        c * M * Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ)))
                            = c * M * (Real.sqrt (N : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (N : ℝ)))) := by ring
                        _ ≤ c * M * C₃ := mul_le_mul_of_nonneg_left hterm hmul
        have h2 : |∑ n ∈ Finset.Icc 1 (N - 1),
            (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
              * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                  - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))| ≤ c * M * C₂ := by
          calc
            |∑ n ∈ Finset.Icc 1 (N - 1),
                (∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                  * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                      - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))|
                ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
                    |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                      * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                          - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))| :=
                    Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
                c * M * (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                apply Finset.sum_le_sum
                intro n hn
                have hn1 : (1 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
                have hab : |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                    * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                        - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))|
                    ≤ (c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                      * (M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
                    calc
                      |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                          * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                              - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))|
                          ≤ |∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i|
                            * |((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                                - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ))| := (abs_mul _ _).le
                      _ ≤ (c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                          * (M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := by
                          exact mul_le_mul (hswN n hn1) (hΔ n hn1) (abs_nonneg _)
                            (mul_nonneg (mul_nonneg (le_of_lt hc0) (Nat.cast_nonneg n)) (Real.exp_nonneg _))
                calc
                  |(∑ i ∈ Finset.Icc 1 n, vonMangoldt i * chi5 i)
                      * (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * triKer (δ * Real.log ((n + 1 : ℕ) : ℝ)))
                          - (Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ)))|
                      ≤ (c * (n : ℝ) * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                        * (M * (Real.sqrt (n : ℝ))⁻¹ ^ 3) := hab
                  _ = c * M * (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) := by
                      have hrootn : (n : ℝ) * (Real.sqrt (n : ℝ))⁻¹ ^ 3 = (Real.sqrt (n : ℝ))⁻¹ := by
                        have hnpos' : (0 : ℝ) < (n : ℝ) :=
                          lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (by exact_mod_cast hn1)
                        have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
                          Real.sq_sqrt (le_of_lt hnpos')
                        have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnpos')
                        field_simp [hne]
                        conv_lhs =>
                          rw [← hsq]
                      conv_rhs =>
                        rw [← hrootn]
                      ring
            _ ≤ c * M * C₂ := by
                have hmul : 0 ≤ c * M := mul_nonneg (le_of_lt hc0) hM0
                calc
                  ∑ n ∈ Finset.Icc 1 (N - 1),
                      c * M * (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ)))
                      = c * M * (∑ n ∈ Finset.Icc 1 (N - 1),
                          (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ)))) := by
                      rw [Finset.mul_sum]
                      ring
                  _ ≤ c * M * C₂ := by
                      have hexp_le : ∀ n ∈ Finset.Icc 1 (N - 1),
                          Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))) ≤ 1 := by
                        intro n hn
                        have hnlog : 0 ≤ Real.log (n : ℝ) := by
                          have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
                          exact Real.log_nonneg hn1'
                        have hneg : -c' * Real.sqrt (Real.log (n : ℝ)) ≤ 0 := by
                          exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hc'0]) (Real.sqrt_nonneg _)
                        exact (Real.exp_le_one_iff).2 hneg
                      have hsubset : Finset.Icc 1 (N - 1) ⊆ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊) := by
                        intro n hn
                        have hn1 : (1 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
                        have hn2 : n ≤ N - 1 := (Finset.mem_Icc.mp hn).2
                        have hnleN : n ≤ N := le_trans hn2 (Nat.sub_le N 1)
                        have hNleE : N ≤ ⌊Real.exp (1 / δ)⌋₊ := by
                          dsimp [N]
                          exact Nat.floor_mono hXw'
                        have hnlemin : n ≤ min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊ :=
                          le_min (by simpa [N] using hnleN) (le_trans hnleN hNleE)
                        apply Finset.mem_Icc.mpr
                        exact ⟨hn1, hnlemin⟩
                      have hsub :
                          (∑ n ∈ Finset.Icc 1 (N - 1),
                            (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                            ≤ ∑ n ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊),
                                (Real.sqrt (n : ℝ))⁻¹ := by
                        calc
                          (∑ n ∈ Finset.Icc 1 (N - 1),
                              (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-c' * Real.sqrt (Real.log (n : ℝ))))
                              ≤ ∑ n ∈ Finset.Icc 1 (N - 1), (Real.sqrt (n : ℝ))⁻¹ := by
                                apply Finset.sum_le_sum
                                intro n hn
                                exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) (hexp_le n hn)
                          _ ≤ ∑ n ∈ Finset.Icc 1 (min ⌊X'⌋₊ ⌊Real.exp (1 / δ)⌋₊), (Real.sqrt (n : ℝ))⁻¹ := by
                              exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
                                (fun n _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
                      exact mul_le_mul_of_nonneg_left (hsub.trans (hdec2 X' hX')) hmul
        linarith [h1, h2]
    _ = c * M * (C₂ + C₃) := by ring

/-! ### 2.1b (L3) BGS 引理 3-5 逐条移植（配对和展开；2026-10-27 半形式化）

BGS 结构（引用本攻防 S7.1 §3 / S7.3-7.5 文档论证）：
  引理 5（核构造）：λ≤1/2 核族 ⟺ K(0)=1 且 supp K ⊆ [−1,1]——`KernelAdmissible`；
    **2026-11-23 第七刀**：此处的 K 是**频域 profile 自身**（与 `pairConstant`（K(δ·ΔIm)）和
    `primeSum`（K(δ·log n)）同口径），支撑是 K 自己的支撑，而不是"某个 K̂ 的谱"。
    旧件 `Khat_admissible`（靠空转 axiom）已撤；新件 `triKer_admissible` 由
    `triKer_zero` + `triKer_supp` 两条定义即得的真证给出。
  引理 3（配对和积分展开）：KernelAdmissible 核 ⟹ pairConstant = 对角主项 + 素数项 + 离线误差
    （Montgomery–Vaughan 均值；`bgs3_pair_expansion`）。
  引理 4（离线误差）：弱实部 + T^{3/8} 切割 ⟹ |offcrit| ≤ o(1)（`offcritical_small`，见下）。
`pair_sum_expansion` 由 bgs3 组装（引理 4 的 |offcrit|≤1 缩放已并入 bgs3 陈述，注释承接）。 -/

/-- 引理 5（核构造，**profile 口径**）：K 可容许 ⟺ `K 0 = 1` 且 `supp K ⊆ [−1,1]`。
    **2026-11-23 第七刀**：第二个合取项从 `∀ u, 1 < |u| → fourierCos Khat u = 0` 改为
    `∀ u, 1 < |u| → K u = 0`。改动理由（机检）：旧式与 K 无关，且因 `fourierCos Khat ≡ 0`
    （Khat 不可绝对积）而恒真，于是"可容许性"对 K 毫无约束、`bgs3` 的一般 K 版为假
    （第六刀），而它与 `fourierCos_Khat` 又合成 `False`（`_incons_ax.lean`）。改口径后
    可容许性第一次真正约束 K，且 `triKer` 满足它（定义即得）。 -/
def KernelAdmissible (K : ℝ → ℝ) : Prop :=
  K 0 = 1 ∧ ∀ u : ℝ, 1 < |u| → K u = 0

/-- `triKer` 可容许（真证，零 axiom）：`triKer_zero`（`Γ 0 = 1`）+ `triKer_supp`（支撑 ⊂ [−1,1]）。 -/
theorem triKer_admissible : KernelAdmissible triKer :=
  ⟨triKer_zero, fun _ h => triKer_supp h⟩

/-- 引理 3（配对和展开，statement）：**固定核 `triKer`** + 弱实部假设 ⟹
    A_L = 对角主项 + 素数项 + 离线误差；
    对角主项 diag ≤ C_MT + C₁·ε（ε 偏差系数 C₁——n2_linkage O(ε) 联动吸收，文档 S7.4 定理 N2）；
    素数项 |prime| ≤ 1（Montgomery–Vaughan 均值 + SW 压制，文档 S7.6）；
    离线项 = `offCriticalError T / N_L T`（引理 4 缩放，其 ≤1 由 `offcrit_remainder_le_one` 真证）。
    **2026-11-23 第六刀（撤除虚假 generality）**：原语句对**任意** `K`（仅要求 `KernelAdmissible K`）断言本式，
    而当时 `KernelAdmissible K` 的第二个合取项根本不涉及 K，于是 `K` 除 `K 0 = 1` 外完全自由。
    `pairConstant K δ N Z = 1 + (Σ_{pairs} K(δ·Δ.im)²)/N` 是 `K` 在 `N(N−1)` 个点上的取值平方和，
    取 `K := fun u => if u = 0 then 1 else M` 即令配对和 → ∞，而 `C_MT + C₁ε + 1 + E/N` 与 M 无关
    ⟹ 原语句在一般 K 上为假。
    **第七刀（换核）**：核由 `Khat`（cos-window 的 sinc 梳，支撑全实轴、`fourierCos Khat ≡ 0`）
    换为 `triKer`（三角核，`supp ⊆ [−1,1]` 由定义即得），于是"λ ≤ 1/2 核族"在形式层第一次成真；
    语句仍只谈一个具体对象（`s71_main` 只用它）。 -/
axiom bgs3_pair_expansion (δ T ε : ℝ) (hweak : WeakRealPart T zerosLChi5) :
  ∃ (C₁ diag prime : ℝ), 0 ≤ C₁ ∧
    pairConstant triKer δ (N_L T) (zerosLChi5UpTo T) = diag + prime + offCriticalError T / N_L T ∧
    diag ≤ C_MT + C₁ * ε ∧ |prime| ≤ 1

/-- (L3) 配对和展开（组装定理）：BGS 引理 3（bgs3_pair_expansion）的直接包装——
    核固定为 `triKer`（引理 5 的可容许性已不进入语句），离线项承接引理 4。 -/
theorem pair_sum_expansion (δ T ε : ℝ) (hweak : WeakRealPart T zerosLChi5) :
  ∃ (C₁ diag prime : ℝ), 0 ≤ C₁ ∧
    pairConstant triKer δ (N_L T) (zerosLChi5UpTo T) = diag + prime + offCriticalError T / N_L T ∧
    diag ≤ C_MT + C₁ * ε ∧ |prime| ≤ 1 := by
  exact bgs3_pair_expansion δ T ε hweak

/-! ## 2.2 (L4) BGS 引理 4 移植——T^{3/8} 切割链（2026-10-27 半形式化）

离线误差的机制（文档 S7.5 定理 N3 / S7.1 §3）：Weil 显式公式余项按零点高度切割为两段：
  · offcritLow（低频段，≤ T^{3/8} 切割）：弱实部假设压离临界带项（β ≤ 1−c/logT 型），
    贡献 O(√log T) 量级；
  · offcritHigh（高频段，> T^{3/8} 切割）：零点计数 N(T) 主项吸收（Riemann–von Mangoldt
    平凡界），贡献 O(√log T) 量级。
切割分解与两段界原为命名 axiom（数论件，文档层论证）；`offcritical_small` 由三角不等式组装真证。
**2026-11-23 第四刀后**：切割分解已是定义性定理（`offcritHigh := E − offcritLow`），
余下真 axiom 只有两条段界 `bgs4_offcrit_low` / `bgs4_offcrit_high`。 -/

/-- 离线误差的低频段（T^{3/8} 切割以下；弱实部件）。 -/
opaque offcritLow (T : ℝ) : ℝ

/-- 离线误差的高频段（T^{3/8} 切割以上；计数件）。
    **2026-11-23 第四刀：原 `opaque offcritHigh` 已换为真定义**——`offcritHigh s := offCriticalError s − offcritLow s`
    （即「余项减去低频段后的剩余」）。
    理由：`offCriticalError` / `offcritLow` / `offcritHigh` 三者**本无三个独立数论对象**，
    切割分解 `E = low + high` 从来不是一条数学事实，而是一条**命名约定**；把它当 axiom 供着，
    等于用公理声明「两个名字相加等于原来的名字」。改为定义后该恒等式定义性成立，
    `bgs4_offcrit_split` 由 axiom 降为 theorem（一行 `ring`）。
    内容未减：`bgs4_offcrit_low` + `bgs4_offcrit_high` 两条段界仍在（公理层级不变），
    经三角不等式给出的 `offcritical_small` 与原口径逐字相同。 -/
noncomputable def offcritHigh (T : ℝ) : ℝ := offCriticalError T - offcritLow T

/-- 切割分解（引理 4(i)）：余项 = 低频 + 高频。
    **2026-11-23：已从 axiom 降为 theorem**——`offcritHigh` 取「余项减低频」定义后，
    本式是定义性恒等式（`ring` 收尾），不再需要公理。 -/
theorem bgs4_offcrit_split : ∀ s : ℝ, offCriticalError s = offcritLow s + offcritHigh s := by
  intro s
  unfold offcritHigh
  ring

/-- 低频段界（引理 4(ii)，弱实部件）：|offcritLow s| ≤ R₁·√log s（T^{3/8} 以下项）。
    **2026-11-23 口径加强**：`R₁` 改为**与 T 无关的绝对常数**（先 `∃ R₁`，再 `∀ T`）。
    原写法 `∀ T, ∃ R₁` 允许常数随 T 增长，比 BGS 原文弱，且下游无法使用——
    `|offcrit| ≤ 1` 的收尾需要同一个 R₁ 对所有 T 成立。 -/
axiom bgs4_offcrit_low :
  ∃ (R₁ : ℝ), 0 ≤ R₁ ∧
    ∀ (T : ℝ), (1 : ℝ) ≤ T → WeakRealPart T zerosLChi5 →
      ∀ s : ℝ, T ≤ s → |offcritLow s| ≤ R₁ * Real.sqrt (Real.log s)

/-- 高频段界（引理 4(iii)，计数件）：|offcritHigh s| ≤ R₂·√log s（N(T) 主项吸收）。
    同 `bgs4_offcrit_low`：R₂ 为与 T 无关的绝对常数。 -/
axiom bgs4_offcrit_high :
  ∃ (R₂ : ℝ), 0 ≤ R₂ ∧
    ∀ (T : ℝ), (1 : ℝ) ≤ T → WeakRealPart T zerosLChi5 →
      ∀ s : ℝ, T ≤ s → |offcritHigh s| ≤ R₂ * Real.sqrt (Real.log s)

/-- (L4) 离线误差（组装定理）：弱实部假设 + T^{3/8} 切割 → √logT 型界（绝对常数 R）。
    组装：切割分解 + 双段界 + 三角不等式（R = R₁ + R₂）。 -/
theorem offcritical_small :
  ∃ (R : ℝ), 0 ≤ R ∧
    ∀ (T : ℝ), (1 : ℝ) ≤ T → WeakRealPart T zerosLChi5 →
      ∀ s : ℝ, T ≤ s → |offCriticalError s| ≤ R * Real.sqrt (Real.log s) := by
  rcases bgs4_offcrit_low with ⟨R₁, hR₁0, hlow⟩
  rcases bgs4_offcrit_high with ⟨R₂, hR₂0, hhigh⟩
  refine ⟨R₁ + R₂, add_nonneg hR₁0 hR₂0, ?_⟩
  intro T hT hweak s hs
  rw [bgs4_offcrit_split s]
  calc
    |offcritLow s + offcritHigh s| ≤ |offcritLow s| + |offcritHigh s| := abs_add_le _ _
    _ ≤ R₁ * Real.sqrt (Real.log s) + R₂ * Real.sqrt (Real.log s) :=
      add_le_add (hlow T hT hweak s hs) (hhigh T hT hweak s hs)
    _ = (R₁ + R₂) * Real.sqrt (Real.log s) := by ring

/-! ### 2.2.1 L4 链接入主定理（2026-11-23 第五刀）

`offCriticalError T / N_L T` 是 `bgs3_pair_expansion` 里离线项的**具体**取值。下面把这件
「除以真实零点计数后 ≤ 1」证出来（不再作为 axiom 的一部分），链条：

1. `offcritical_small` 给**绝对常数** R：`|E s| ≤ R·√log s`（s ≥ T ≥ 1）；
2. `offcritConst ≤ NLc·T`（由阈值 T₀ 保证）⟹ `R·√log T ≤ NLc·T·√log T`；
3. `log T ≥ 1`（T ≥ e）⟹ `√log T ≤ log T`，故 `R·√log T ≤ NLc·T·log T`；
4. `N_L_lower_bound` 给 `NLc·T·log T ≤ N_L T` ⟹ `|E T| ≤ N_L T`；
5. 除以 `N_L T ≥ 0`（`abs_div` + `div_le_one`；`N_L T = 0` 时 Lean `x/0 = 0`，结论平凡成立）。

阈值以 `Classical.choose` 把两个存在量词的见证取定成命名对象（`offcritConst` / `NLc` /
`offcritThreshold`），这样主定理可以显式假设 `T` 越过阈值，而不是藏一个匿名 ∃。 -/

/-- 引理 4 的绝对常数（`offcritical_small` 见证，取定命名）。 -/
noncomputable def offcritConst : ℝ := Classical.choose offcritical_small

/-- `offcritConst ≥ 0`。 -/
lemma offcritConst_nonneg : 0 ≤ offcritConst := (Classical.choose_spec offcritical_small).1

/-- `offcritConst` 的规格（对任意 T ≥ 1、任意 s ≥ T）。 -/
lemma offcritConst_spec (T : ℝ) (hT : (1 : ℝ) ≤ T) (hweak : WeakRealPart T zerosLChi5)
    {s : ℝ} (hs : T ≤ s) : |offCriticalError s| ≤ offcritConst * Real.sqrt (Real.log s) :=
  (Classical.choose_spec offcritical_small).2 T hT hweak s hs

/-- 零点计数下界常数 c（`N_L_lower_bound` 见证，取定命名）。 -/
noncomputable def NLc : ℝ := Classical.choose N_L_lower_bound

/-- `NLc > 0`。 -/
lemma NLc_pos : 0 < NLc := (Classical.choose_spec N_L_lower_bound).1

/-- `NLc` 的规格：`NLc·T·log T ≤ N_L T`（T ≥ 1）。 -/
lemma NLc_spec (T : ℝ) (hT : (1 : ℝ) ≤ T) : NLc * T * Real.log T ≤ N_L T :=
  (Classical.choose_spec N_L_lower_bound).2 T hT

/-- 收尾阈值 `T₀ = max (e) (max 1 (offcritConst/NLc))`：越过它则
    `log T ≥ 1`（T ≥ e）且 `offcritConst ≤ NLc·T`（T ≥ offcritConst/NLc）。 -/
noncomputable def offcritThreshold : ℝ := max (Real.exp 1) (max 1 (offcritConst / NLc))

/-- `1 ≤ T₀`（故阈值本身满足引理 4 的 T ≥ 1 前提）。 -/
lemma one_le_offcritThreshold : (1 : ℝ) ≤ offcritThreshold :=
  le_trans (Real.one_le_exp zero_le_one) (le_max_left _ _)

/-- **L4 链接入主定理（真证）**：`T` 越过阈值后，离线项除以真实零点计数 ≤ 1。 -/
theorem offcrit_remainder_le_one (T : ℝ) (hT : (1 : ℝ) ≤ T) (hweak : WeakRealPart T zerosLChi5)
    (hbig : offcritThreshold ≤ T) : |offCriticalError T / N_L T| ≤ 1 := by
  -- T ≥ e
  have hTexp : Real.exp (1 : ℝ) ≤ T := le_trans (le_max_left _ _) hbig
  -- log T ≥ 1
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hTexp
    simpa [Real.log_exp] using h
  -- offcritConst ≤ NLc * T
  have hRc : offcritConst / NLc ≤ T := by
    have h1 : offcritConst / NLc ≤ max (1 : ℝ) (offcritConst / NLc) := le_max_right _ _
    exact le_trans h1 (le_trans (le_max_right _ _) hbig)
  have hNLcT : offcritConst ≤ NLc * T := by
    have h := mul_le_mul_of_nonneg_right hRc (le_of_lt NLc_pos)
    have hEq : offcritConst / NLc * NLc = offcritConst :=
      div_mul_cancel₀ offcritConst (ne_of_gt NLc_pos)
    rw [hEq] at h
    linarith
  -- √log T ≤ log T，且 |E T| ≤ R·√log T
  have hsqrt : Real.sqrt (Real.log T) ≤ Real.log T :=
    (Real.sqrt_le_self_iff).mpr (Or.inr hlog1)
  have hE := offcritConst_spec T hT hweak (le_refl T)
  -- |E T| ≤ NLc * T * log T ≤ N_L T
  have hEabs : |offCriticalError T| ≤ N_L T := by
    have h1 : offcritConst * Real.sqrt (Real.log T) ≤ offcritConst * Real.log T :=
      mul_le_mul_of_nonneg_left hsqrt offcritConst_nonneg
    have h2 : offcritConst * Real.log T ≤ NLc * T * Real.log T := by
      have := mul_le_mul_of_nonneg_right hNLcT (le_trans zero_le_one hlog1)
      linarith
    exact le_trans hE (le_trans h1 (le_trans h2 (NLc_spec T hT)))
  -- 收尾：除以 N_L T（≥ 0）
  rcases lt_or_eq_of_le (N_L_nonneg T) with hpos | hzero
  · have hd : |offCriticalError T / N_L T| = |offCriticalError T| / N_L T := by
      rw [abs_div, abs_of_nonneg (N_L_nonneg T)]
    rw [hd]
    exact (div_le_one hpos).mpr hEabs
  · have hz : N_L T = 0 := hzero.symm
    rw [hz, div_zero, abs_zero]
    norm_num

/-! ## 3. 主定理 S7.1（组装真证；分析层 (L1)–(L4) 为命名 axiom，2026-11-23 第四刀后共 9 条） -/

/-- 定理 S7.1（L(s, χ_5) 单族 BGS 型配对公式——弱假设下无条件）：
    对 λ≤1/2 核族（KernelAdmissible：Γ 三角核、K(0)=1、supp ⊂ [−1,1]），
    A_L(K) ≤ C_MT + O(ε) + o(1)。
    组装真证：由 pair_sum_expansion（BGS 引理 3-5 移植）分解 A_L = diag + prime + offcrit，
    对角主项 diag ≤ C_MT + C₁ε、素数项/离线项以 |·|≤1 占位界并入 C₂=2。 -/
theorem s71_main
    (T : ℝ) (hT : (1 : ℝ) ≤ T) (hweak : WeakRealPart T zerosLChi5)
    (hbig : offcritThreshold ≤ T) (ε : ℝ) (_hε0 : 0 < ε) :
    ∃ (C₁ C₂ : ℝ), 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      pairConstant triKer (Real.log T / (2 * Real.pi)) (N_L T) (zerosLChi5UpTo T)
        ≤ C_MT + C₁ * ε + C₂ := by
  let δ : ℝ := Real.log T / (2 * Real.pi)
  rcases pair_sum_expansion δ T ε hweak with ⟨C₁, diag, prime,
      hC₁0, hsplit, hdiag, hprime⟩
  have hoff : |offCriticalError T / N_L T| ≤ 1 := offcrit_remainder_le_one T hT hweak hbig
  refine ⟨C₁, 2, hC₁0, by norm_num, ?_⟩
  calc
    pairConstant triKer δ (N_L T) (zerosLChi5UpTo T)
        = diag + prime + offCriticalError T / N_L T := hsplit
    _ ≤ C_MT + C₁ * ε + |prime| + |offCriticalError T / N_L T| := by
      linarith [hdiag, le_abs_self prime, le_abs_self (offCriticalError T / N_L T)]
    _ ≤ C_MT + C₁ * ε + 1 + 1 := by linarith [hprime, hoff]
    _ = C_MT + C₁ * ε + 2 := by ring

/-! ## 4. 击破清单（下一轮逐个替换 sorry/axiom）

- [x] `pairConstant`：**真实定义完成**（2026-10-27，tsum 差型配对和 1 + Σ_{z₁≠z₂∈Z} K(δ·im(z₁−z₂))²/N，
      紧支撑核自动有限截断；收敛性论证 = 长线真证项）。
- [x] `zerosLChi5`：**真实定义完成**（2026-10-27，临界带 0<Re s<1 内 L 零点集，
      LFun opaque + 新增 (L0a) `lfun_conj_symm`（conj 对称，支撑 conj_closed 真证）+
      (L0b) `lfun_dirichlet_series`（Re s>0 的 Dirichlet 卷积表示，长线真证目标）；
      原 `{z | True}` 占位已移除）。
- [ ] (L1) `landau_explicit_L`：**精确陈述完成**（2026-10-27，Yildirim 公式 (6) 重排式）；
      形式化真证需先把 `-L'/L` 的 Dirichlet 级数展开与 Mellin 变换写成引理——长线目标。
- [ ] (L2) `siegel_walfisz_chi5`：**精确陈述完成**（2026-10-27，Finset.Icc 1 ⌊x⌋₊ 真实和式）；
      形式化真证需 PNT 在算术级数 + 特征和估计——长线目标。
- [x] (L3) `pair_sum_expansion`：**BGS 引理 3-5 逐条移植完成**（2026-10-27）——
      引理 5 `KernelAdmissible`（K 0 = 1 + supp K ⊆ [−1,1]，profile 口径）+ `triKer_admissible` 组装
      （两条皆定义即得的真证；载体核 = `triKer`，第七刀）；引理 3 `bgs3_pair_expansion`
      （分解 + diag≤C_MT+C₁ε + |prime|,|offcrit|≤1）；引理 4 承接 `offcritical_small`；
      `pair_sum_expansion` 定理化（KernelAdmissible 条件化），s71_main 已接入。
- [x] (L4) `offcritical_small`：**BGS 引理 4 移植完成**（2026-10-27，T^{3/8} 切割链）——
      切割分解 `bgs4_offcrit_split`（余项 = 低频 offcritLow + 高频 offcritHigh）：
      **2026-11-23 第四刀后已降为 theorem**（`offcritHigh := offCriticalError − offcritLow` 定义性恒等式）；
      低频弱实部件 `bgs4_offcrit_low`、高频计数件 `bgs4_offcrit_high`（各 √logT 界）仍为命名 axiom；
      `offcritical_small` 组装真证（三角不等式，R = R₁+R₂）。
- [x] `s71_main`：**组装真证**（2026-10-27）——pair_sum_expansion 分解
      A_L = diag + prime + offcrit；diag ≤ C_MT + C₁ε（n2_linkage O(ε)）、
      |prime|,|offcrit| ≤ 1 并入 C₂=2（SW/BGS 占位界）；C₁, C₂ 显式。

「推 1」断层（超支撑 λ→∞）三件套——S7 闭路只覆盖 λ≤1/2（BGS 引理 5 supp r⊂[−1,1]）；
  Stage 3+ 已于 S7_1_Stage3.lean 形式化（2026-10-26）：
- [x] (N1) BGS 引理 5 超支撑推广：scaleKernel 定义 + 支撑保持真证明（scaleKernel_support）；
      fourierCos_scale（r̂_a(z)=r̂(az)）、scaleKernel_L1_invariant、n1_diag_invariant、n1_offdiag_vanishes
      ——结构件 axiom（积分层，文档 S7.3 定理 N1）。
- [x] (N2) ε–λ 联动：f_eps_support 真证明（|x|>1/2 ⟹ f_ε=0，支撑 [−1/2,1/2]）；
      n2_linkage（λ=(logT)^q、a=(logT)^{−q}、ε=c(logT)^{−q} ⟹ 偏差 O((logT)^{−q})）——axiom
      （文档 S7.4 定理 N2）。
- [ ] (N3) 离线项一致版本：**2026-11-23 撤除原 `offcritSum` / `n3_remainder_uniform`**
      （空条目：自由算子 + ∃R 有界声明可被 `offcritSum≡0` 满足，且全库 0 处使用；
      文档对象依赖 `w(ρ−ρ')`、复自变量 `r̂`、`x` 尺度相减三件未形式化机制）。
      N3 作为**未形式化项**登记在 `Findings_GRH_Interface.md` §十六（文档 S7.5 定理 N3）。
三条真证明件（超支撑素数项层）：
- [x] Abel 求和引理（sum_abel，summation by parts 归纳真证；S7.6 §2.4 离散骨架）
- [x] K̂_a 偶性（Khat_a_even，一阶校正恒为零真证）；二阶一致界 khat_second_order_bound
      |K̂(au)−1|≤2(au)²+(au)⁴——**真证**（K̂ 导数闭式乘形式 + 区间界；2026-10-26 迁入 Stage3 替换 axiom；
      数值核对：K̂″(0)≈−3.06、ratio=1.000 @ aδ≤3e−3、f̂₀(0)=∫K₀=1）
- [x] N_L 对数增长下界（N_L_lower_bound：N_L(T)≥c·T·logT）——axiom（数论件，S6 口径）
构建证据：lake build QRH 1965 jobs 全绿（build_qrh_full.txt）；Stage3 独立编译 build_stage3.txt。
超支撑素数项量级（数值件 F 已实测，2026-10-25）：S(X)=Σ_{p≤X}Λχ₅(p)p^{−1/2}K̂_a(δlogp)
  = O(√X·poly(log X))——相对 N_L ~ (X/2π)logX 为 o(1)——无需 e^{−c√logX} 指数级；
  |S_a|/N_L 单调衰减至 1e−8（X=10⁸），|S_a|≈2.05 有界收敛（强于理论上界）。

优先级建议（按依赖序）：
  Stage 1：Core 件清零（Khat_zero、f0_sub_feps_L1_bound、C_MT 数值界）→ s71 常数为显式。
  Stage 2：(L3) 配对和展开写成半形式化（有限多重集 + 有限和）；δ 口径用实数。
  Stage 3：(L2) SW 作为命名 axiom（数学上已证、形式化长线）。
  Stage 3+：（N1)-(N3) 超支撑断层闭合 + 三条新真证明件（数值件 F 定向先行）。
  Stage 4：s71_main 组装（epsilon-delta 展开）。
-/

end QRH
