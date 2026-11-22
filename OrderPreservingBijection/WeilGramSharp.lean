/-
Sharpen the `‖φ̂‖²` bound: on the **upper half-plane** the phase `e^{Iρx}` has modulus
`e^{-(Im ρ)·x} ≤ 1` for `x ∈ [0,1]`, so the crude factor `exp ‖ρ‖` (hence `exp(2T)` in `hz`)
is unnecessary there. This is the same normalisation lesson as (I.16)-(I.17) of the
Alpöge–Claude exposition: choose the normalisation so that the size side is *exact*
(`‖z^a‖² = a!`) instead of an exponential in the height.

Boundary (must be read with it):
* only for zeros with `Im ρ ≥ 0`; the lower half-plane needs the conjugate argument, which
  is not formalised here (for a symmetric `S` the two halves are equal in modulus when `φ`
  is real-valued, still to be written);
* the diagonal truncation `‖φ̂_j(ρ)‖²` and the missing `j ≠ k` terms are unchanged from
  `WeilGramConcrete.lean`.
-/

import OrderPreservingBijection.WeilGramConcrete

open MeasureTheory
open Matrix

set_option maxHeartbeats 1000000

namespace RHSpectralDuality

/-! ### 一、上半平面上的相位估计 -/

/-- 相位 `I·ρ·x` 的实部是 `-(Im ρ)·x`。 -/
theorem phase_re_eq (ρ : ℂ) (x : ℝ) :
    (Complex.I * ρ * (x : ℂ)).re = -(ρ.im * x) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `0 ≤ Im ρ`、`0 ≤ x` 时相位实部 `≤ 0`。 -/
theorem phase_re_nonpos {ρ : ℂ} {x : ℝ} (hρ : 0 ≤ ρ.im) (hx0 : 0 ≤ x) :
    (Complex.I * ρ * (x : ℂ)).re ≤ 0 := by
  rw [phase_re_eq]
  have : 0 ≤ ρ.im * x := mul_nonneg hρ hx0
  linarith

/-- `0 ≤ Im ρ`、`x ≥ 0` 时 `‖e^{Iρx}‖ ≤ 1`。 -/
theorem phase_norm_le_one {ρ : ℂ} {x : ℝ} (hρ : 0 ≤ ρ.im) (hx0 : 0 ≤ x) :
    ‖Complex.exp (Complex.I * ρ * (x : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have h := phase_re_nonpos hρ hx0
  calc Real.exp (Complex.I * ρ * (x : ℂ)).re ≤ Real.exp 0 := Real.exp_le_exp.mpr h
    _ = 1 := Real.exp_zero

/-! ### 二、`‖φ̂‖` 与 `‖φ̂‖²` 的上半平面版本（常数从 `exp ‖ρ‖` 降到 `1`） -/

/-- **`φ̂` 的 L¹ 上界（上半平面，常数 1）**：`‖φ̂(ρ)‖ ≤ ∫₀¹ ‖φ‖`，只要 `0 ≤ Im ρ`。 -/
theorem phiHat_norm_le_one (φ : ℝ → ℂ) (hφ : Continuous φ) {ρ : ℂ} (hρ : 0 ≤ ρ.im) :
    ‖phiHat φ ρ‖ ≤ ∫ x in (0 : ℝ)..1, ‖φ x‖ := by
  have hphase : Continuous (fun x : ℝ => Complex.exp (Complex.I * ρ * (x : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have h1 : Continuous (fun x : ℝ => φ x * Complex.exp (Complex.I * ρ * (x : ℂ))) :=
    hφ.mul hphase
  have h2 : Continuous (fun x : ℝ => ‖φ x‖) := hφ.norm
  calc ‖∫ x in (0 : ℝ)..1, φ x * Complex.exp (Complex.I * ρ * (x : ℂ))‖
      ≤ ∫ x in (0 : ℝ)..1, ‖φ x * Complex.exp (Complex.I * ρ * (x : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ x in (0 : ℝ)..1, ‖φ x‖ := by
        refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ ?_
        · exact h1.norm.intervalIntegrable (μ := volume) 0 1
        · exact h2.intervalIntegrable (μ := volume) 0 1
        · intro x hx
          obtain ⟨hx0, _hx1⟩ := hx
          rw [norm_mul]
          calc ‖φ x‖ * ‖Complex.exp (Complex.I * ρ * (x : ℂ))‖
              ≤ ‖φ x‖ * 1 :=
                mul_le_mul_of_nonneg_left (phase_norm_le_one hρ hx0) (norm_nonneg _)
            _ = ‖φ x‖ := mul_one _

/-- **`‖φ̂‖²` 的上界（上半平面）**：`‖φ̂(ρ)‖² ≤ (∫₀¹ ‖φ‖)²`，`0 ≤ Im ρ`。 -/
theorem phiHat_sq_le_one (φ : ℝ → ℂ) (hφ : Continuous φ) {ρ : ℂ} (hρ : 0 ≤ ρ.im) :
    ‖phiHat φ ρ‖ ^ 2 ≤ (∫ x in (0 : ℝ)..1, ‖φ x‖) ^ 2 := by
  have h := phiHat_norm_le_one φ hφ hρ
  have hI := integral_norm_nonneg φ hφ
  exact sq_le_sq' (by linarith [norm_nonneg (phiHat φ ρ)]) h

/-! ### 三、`hz` 的上界：`card S · (∫‖φ_j‖)^2`，不再带 `exp(2T)` -/

/-- **零点侧对角的上界（上半平面零点）**：`S` 全在 `Im ρ ≥ 0` 时
    `hz_j ≤ card S · (∫₀¹ ‖φ_j‖)²`。对照 `weilZeroDiag_re_le` 的 `card S · (exp T)² · …`：
    指数因子在这个区域里被消掉了。 -/
theorem weilZeroDiag_re_le_upper {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset ℂ) (φ : n → ℝ → ℂ) (hφ : ∀ j, Continuous (φ j))
    (hS : ∀ ρ ∈ S, 0 ≤ ρ.im) (j : n) :
    (weilZeroDiag S φ j).re ≤ (S.card : ℝ) * (∫ x in (0 : ℝ)..1, ‖φ j x‖) ^ 2 := by
  rw [weilZeroDiag, Complex.ofReal_re]
  calc ∑ ρ ∈ S, ‖phiHat (φ j) ρ‖ ^ 2
      ≤ ∑ _ρ ∈ S, (∫ x in (0 : ℝ)..1, ‖φ j x‖) ^ 2 :=
        Finset.sum_le_sum (fun ρ hρ => phiHat_sq_le_one (φ j) (hφ j) (hS ρ hρ))
    _ = S.card • ((∫ x in (0 : ℝ)..1, ‖φ j x‖) ^ 2) := Finset.sum_const _
    _ = (S.card : ℝ) * (∫ x in (0 : ℝ)..1, ‖φ j x‖) ^ 2 := by rw [nsmul_eq_mul]

end RHSpectralDuality

#print axioms RHSpectralDuality.phase_re_eq
#print axioms RHSpectralDuality.phase_re_nonpos
#print axioms RHSpectralDuality.phase_norm_le_one
#print axioms RHSpectralDuality.phiHat_norm_le_one
#print axioms RHSpectralDuality.phiHat_sq_le_one
#print axioms RHSpectralDuality.weilZeroDiag_re_le_upper
