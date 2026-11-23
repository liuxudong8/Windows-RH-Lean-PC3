import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Analytic.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open scoped Topology
open Filter
/-!
# 实系数 L 级数在共轭下的对称性（`lfun_conj_symm` 证明第 ② 步）

内容（自下而上三层，全部真证，无 sorry/axiom）：

1. `conj_eq_self_of_im_eq_zero`：虚部为 0 的复数等于其共轭；
2. `term_conj_of_real_coeff`：实系数时 `LSeries.term f (conj s) n = conj (LSeries.term f s n)`
   （核心是 `ℂ.cpow_conj` + `natCast_arg = 0 ≠ π`：正实数底的 `n^{-s}` 与其共轭互逆）；
3. `LSeries_conj_of_real_coeff`：`LSeries f (conj s) = conj (LSeries f s)`（`Complex.conj_tsum` 换序）；
4. `LFunction_conj_of_real_coeff`：`1 < re s` 时 `LFunction χ (conj s) = conj (LFunction χ s)`
   （`LFunction_eq_LSeries` 把两侧化到第 3 层）。

边界：第 4 层只覆盖收敛半平面 `1 < re s`。全平面的共轭对称需解析延拓唯一性（第 ③ 步）。
-/

open Complex
open scoped LSeries.notation

namespace LSeriesConj

/-- 虚部为 0 的复数等于其共轭。 -/
lemma conj_eq_self_of_im_eq_zero {z : ℂ} (h : z.im = 0) : starRingEnd ℂ z = z := by
  refine Complex.ext ?_ ?_
  · simp
  · simp [h]

/-- **term 层**：实系数时，第 `n` 项在 `conj s` 处的值等于其在 `s` 处值的共轭。 -/
lemma term_conj_of_real_coeff {f : ℕ → ℂ} (hf : ∀ n, (f n).im = 0) (s : ℂ) (n : ℕ) :
    LSeries.term f (starRingEnd ℂ s) n = starRingEnd ℂ (LSeries.term f s n) := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀ (starRingEnd ℂ)]
    have hfx : starRingEnd ℂ (f n) = f n := conj_eq_self_of_im_eq_zero (hf n)
    rw [hfx]
    have hcp : starRingEnd ℂ ((n : ℂ) ^ s) = (n : ℂ) ^ (starRingEnd ℂ s) := by
      have h := Complex.cpow_conj (n : ℂ) s (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne)
      rw [Complex.conj_natCast] at h
      exact h.symm
    rw [hcp]

/-- **级数层**：实系数 L 级数在共轭下取共轭（`tsum` 与 `conj` 交换，无条件成立）。 -/
lemma LSeries_conj_of_real_coeff {f : ℕ → ℂ} (hf : ∀ n, (f n).im = 0) (s : ℂ) :
    LSeries f (starRingEnd ℂ s) = starRingEnd ℂ (LSeries f s) := by
  simp only [LSeries]
  rw [show (∑' n, LSeries.term f (starRingEnd ℂ s) n)
      = ∑' n, starRingEnd ℂ (LSeries.term f s n) from
        tsum_congr (fun n => term_conj_of_real_coeff hf s n)]
  exact (Complex.conj_tsum (fun n => LSeries.term f s n)).symm

/-- **L 函数层**（`1 < re s`）：实值 Dirichlet 特征 ⇒ `L(conj s) = conj (L s)`。 -/
theorem LFunction_conj_of_real_coeff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : ∀ n : ℕ, (χ (n : ZMod N)).im = 0) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ (starRingEnd ℂ s)
      = starRingEnd ℂ (DirichletCharacter.LFunction χ s) := by
  have hsc : (starRingEnd ℂ s).re = s.re := by simp
  rw [DirichletCharacter.LFunction_eq_LSeries χ
      (show 1 < (starRingEnd ℂ s).re by rw [hsc]; exact hs),
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_conj_of_real_coeff hχ s

/-- **全平面共轭对称**（`χ` 实值且非平凡）：
    `L(conj s) = conj (L s)` 对**所有** `s : ℂ` 成立。

    方法（mathlib `riemannZeta_conj` 同款）：`χ ≠ 1` 时 `LFunction χ` 在整个 ℂ 上全纯，
    于是 `f = LFunction χ` 与 `g = conj ∘ f ∘ conj` 都在 `univ` 上解析（后者来自
    `differentiableAt_conj_conj_iff`）；两者在开集 `{1 < re z}` 上相等（第 4 层结论取共轭），
    由解析延拓唯一性（`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`）在连通集 `univ` 上相等。 -/
theorem LFunction_conj_global {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : ∀ n : ℕ, (χ (n : ZMod N)).im = 0) (hne : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ (starRingEnd ℂ s)
      = starRingEnd ℂ (DirichletCharacter.LFunction χ s) := by
  have hf_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ => ((DirichletCharacter.differentiable_LFunction hne) z).differentiableWithinAt) isOpen_univ
  have hg_an : AnalyticOnNhd ℂ (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)))
      Set.univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ => (differentiableAt_conj_conj_iff.mpr
        ((DirichletCharacter.differentiable_LFunction hne) _)).differentiableWithinAt)
      isOpen_univ
  have hgz : ∀ z : ℂ, 1 < z.re →
      starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))
        = DirichletCharacter.LFunction χ z := by
    intro z hz
    have h := LFunction_conj_of_real_coeff χ hχ hz
    simpa using congrArg (starRingEnd ℂ) h
  have hev : (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)))
      =ᶠ[𝓝 (2 : ℂ)] (DirichletCharacter.LFunction χ) := by
    filter_upwards [((isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < 2))] with z hz
    exact hgz z hz
  have heq := AnalyticOnNhd.eq_of_eventuallyEq hg_an hf_an hev
  have h := congrFun heq s
  simpa using congrArg (starRingEnd ℂ) h

end LSeriesConj
