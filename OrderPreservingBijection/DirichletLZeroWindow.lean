/-
  抽取自 Alpöge–Claude 归档：
    Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZerosInWindowFiniteAndPosOrder.lean
  以及 Development/AbelianVarietyTheory/Definitions/Foundations/RayPrimes.lean 中的两个定义。

  这两处只用到 Mathlib 层的事实（解析恒等定理 / 紧致性 / 零点阶），
  因此可以剥掉归档的 5 条 // 冗余 import，变成零依赖模块。

  用途：QRH 的 `zerosLChi5_bounded_finite` 目前是 axiom；本模块给出
  对**任意**模 q、任意特征 χ 的窗口零点有限性 + 零点阶 ≥ 1（正的），
  对 χ₅（q = 5）可直接实例化。
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.DiscreteSubset

noncomputable section

open Complex DirichletCharacter

namespace QRHZeroWindow

/-- 窗口零点集：临街带内、虚部落在以 t 为中心半径 T 的竖带中的全部零点。 -/
def zerosIn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}

/-- 零点重数（解析零点阶）。 -/
def zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

theorem analyticOff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
  intro s hs
  exact (χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt

theorem exists_entire {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 1 ≠ 0 ∧ ∀ s, s ≠ 1 → LFunction χ s = 0 → F s = 0 := by
  by_cases h : χ = 1
  · subst h
    refine ⟨LFunctionTrivChar₁ q, differentiable_LFunctionTrivChar₁ q,
      LFunctionTrivChar₁_apply_one_ne_zero q, fun s hs h0 => ?_⟩
    rw [LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, h0, mul_zero]
  · exact ⟨LFunction χ, differentiable_LFunction h, DirichletCharacter.LFunction_apply_one_ne_zero (χ := χ) h,
      fun _ _ h0 => h0⟩

theorem ne_one_of_mem {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {t T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosIn χ t T) : ρ ≠ 1 := by
  rintro rfl
  have h2 := h.2.1
  simp at h2

theorem finite_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) :
    (zerosIn χ t T).Finite := by
  obtain ⟨F, hF, h1, h0⟩ := exists_entire χ
  have hA : AnalyticOnNhd ℂ F Set.univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  by_contra hinf
  have hinf : (zerosIn χ t T).Infinite := hinf
  have hsub : zerosIn χ t T ⊆ Metric.closedBall (0 : ℂ) (1 + |t| + T) := by
    rintro ρ ⟨h0, h1, h2, -⟩
    rw [mem_closedBall_zero_iff]
    have := Complex.norm_le_abs_re_add_abs_im ρ
    have h3 : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h4 : |ρ.im| ≤ |t| + T := by
      have := abs_sub_abs_le_abs_sub ρ.im t
      linarith
    linarith
  obtain ⟨z, -, hz⟩ := hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall _ _) hsub
  have hfr : ∃ᶠ w in nhdsWithin z {z}ᶜ, F w = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hz
    exact hz.mono fun w hw => h0 w (ne_one_of_mem hw) hw.2.2.2
  have := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hfr
  exact h1 (this (Set.mem_univ 1))

theorem order_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  intro ht
  rw [analyticOrderAt_eq_top] at ht
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have := (analyticOff χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hρ ht
  exact χ.LFunction_ne_zero_of_one_le_re (s := 2) (Or.inr h2) (by simp) (this h2)

theorem one_le_zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosIn χ t T) : 1 ≤ zmult χ ρ := by
  unfold zmult analyticOrderNatAt
  have h1 := order_ne_top χ (ne_one_of_mem hρ)
  have h2 : analyticOrderAt (LFunction χ) ρ ≠ 0 := by
    rw [analyticOrderAt_ne_zero]
    exact ⟨analyticOff χ ρ (ne_one_of_mem hρ), hρ.2.2.2⟩
  rw [Nat.one_le_iff_ne_zero]
  simp [h1, h2]

theorem finite_and_one_le_zmult :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ),
      (zerosIn χ t T).Finite ∧ ∀ ρ ∈ zerosIn χ t T, 1 ≤ zmult χ ρ :=
  fun _ _ χ t T => ⟨finite_zeros χ t T, fun _ hρ => one_le_zmult χ hρ⟩

/-- 口径搬运件：任何"在窗口上等于真实 L 函数"的代理函数 `f`，
其零点集在竖带内同样有限。QRH 侧 `LFun` 目前是 `opaque`，
此件把"有限性"从 `LFun` 的定义方式上解耦：
只需一条同一性假设 `∀ z, f z = LFunction χ z` 即可。 -/
theorem finite_zeros_of_eq_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (f : ℂ → ℂ) (hf : ∀ z, f z = DirichletCharacter.LFunction χ z) (t T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ f ρ = 0}.Finite := by
  have hset : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ f ρ = 0}
      = zerosIn χ t T := by
    ext ρ
    show (0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ f ρ = 0) ↔
      (0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0)
    rw [hf ρ]
  rw [hset]
  exact finite_zeros χ t T

end QRHZeroWindow
