import QRH.S7_1_Core
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory

namespace QRH

/-! #### A4 辅助件（三角核余弦变换闭式） -/

lemma triKer_eq_zero_of_notMem_Icc {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : triKer x = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have h1 : 1 < |x| := by
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  exact triKer_supp h1

lemma triKer_of_abs_le_one {x : ℝ} (h : |x| ≤ 1) : triKer x = 1 - |x| := by
  unfold triKer
  exact max_eq_right (by linarith)

lemma continuous_triKer : Continuous triKer := by
  unfold triKer
  fun_prop

lemma integral_one_sub_mul_cos (c : ℝ) (hc : c ≠ 0) :
    ∫ x in (0 : ℝ)..1, (1 - x) * Real.cos (c * x) = (1 - Real.cos c) / c ^ 2 := by
  have hsin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.sin (c * y)) (Real.cos (c * x) * c) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa [mul_one] using (hasDerivAt_id x).const_mul c
    exact (Real.hasDerivAt_sin (c * x)).comp x hinner
  have hcos : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.cos (c * y)) (-(Real.sin (c * x) * c)) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa [mul_one] using (hasDerivAt_id x).const_mul c
    exact ((Real.hasDerivAt_cos (c * x)).comp x hinner).congr_deriv (by ring)
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => c * (1 - y)) (-c) x := by
    intro x
    have hid : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x
    simpa [mul_one] using (hid.const_sub (1 : ℝ)).const_mul c
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => c * (1 - y) * Real.sin (c * y) - Real.cos (c * y))
        (c ^ 2 * ((1 - x) * Real.cos (c * x))) x := by
    intro x _
    have hprod : HasDerivAt (fun y : ℝ => c * (1 - y) * Real.sin (c * y))
        ((-c) * Real.sin (c * x) + (c * (1 - x)) * (Real.cos (c * x) * c)) x :=
      (hlin x).mul (hsin x)
    refine (hprod.sub (hcos x)).congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun x : ℝ => c ^ 2 * ((1 - x) * Real.cos (c * x))) volume (0 : ℝ) 1 :=
    (by fun_prop : Continuous fun x : ℝ => c ^ 2 * ((1 - x) * Real.cos (c * x))).intervalIntegrable _ _
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hmain
  have hval : (fun y : ℝ => c * (1 - y) * Real.sin (c * y) - Real.cos (c * y)) 1
      - (fun y : ℝ => c * (1 - y) * Real.sin (c * y) - Real.cos (c * y)) 0 = 1 - Real.cos c := by
    simp [Real.sin_zero, Real.cos_zero]
    ring
  rw [hval] at hmain
  refine (eq_div_iff (pow_ne_zero 2 hc)).mpr ?_
  simpa [mul_comm] using hmain

lemma integral_symm_zero_one (f : ℝ → ℝ) (hcont : Continuous f) (heven : ∀ x : ℝ, f (-x) = f x) :
    ∫ x in (-1 : ℝ)..1, f x = 2 * ∫ x in (0 : ℝ)..1, f x := by
  have h1 : IntervalIntegrable f volume (-1 : ℝ) 0 := hcont.intervalIntegrable _ _
  have h2 : IntervalIntegrable f volume (0 : ℝ) 1 := hcont.intervalIntegrable _ _
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hneg : ∫ x in (-1 : ℝ)..0, f (-x) = ∫ x in (0 : ℝ)..1, f x := by
    have := intervalIntegral.integral_comp_neg (f := f) (a := (-1 : ℝ)) (b := 0)
    simpa using this
  have hcongr : ∫ x in (-1 : ℝ)..0, f (-x) = ∫ x in (-1 : ℝ)..0, f x := by
    apply intervalIntegral.integral_congr
    intro x _
    exact heven x
  rw [← hadd, ← hcongr, hneg]
  ring

lemma integral_triKer_mul_cos (c : ℝ) (hc : c ≠ 0) :
    ∫ x in (-1 : ℝ)..1, triKer x * Real.cos (c * x) = 2 * ((1 - Real.cos c) / c ^ 2) := by
  have hcont : Continuous fun x : ℝ => triKer x * Real.cos (c * x) :=
    continuous_triKer.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have heven : ∀ x : ℝ, (fun y : ℝ => triKer y * Real.cos (c * y)) (-x)
      = (fun y : ℝ => triKer y * Real.cos (c * y)) x := by
    intro x
    simp only [triKer, abs_neg, mul_neg, Real.cos_neg]
  have hs := integral_symm_zero_one (fun x : ℝ => triKer x * Real.cos (c * x)) hcont heven
  have h01 : ∫ x in (0 : ℝ)..1, triKer x * Real.cos (c * x)
      = ∫ x in (0 : ℝ)..1, (1 - x) * Real.cos (c * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hmem : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    obtain ⟨h0, h1'⟩ := Set.mem_Icc.mp hmem
    show triKer x * Real.cos (c * x) = (1 - x) * Real.cos (c * x)
    rw [triKer_of_abs_le_one (abs_le.mpr ⟨by linarith, h1'⟩), abs_of_nonneg h0]
  calc ∫ x in (-1 : ℝ)..1, triKer x * Real.cos (c * x)
      = 2 * ∫ x in (0 : ℝ)..1, triKer x * Real.cos (c * x) := hs
    _ = 2 * ∫ x in (0 : ℝ)..1, (1 - x) * Real.cos (c * x) := by rw [h01]
    _ = 2 * ((1 - Real.cos c) / c ^ 2) := by rw [integral_one_sub_mul_cos c hc]

lemma integral_triKer : ∫ x in (-1 : ℝ)..1, triKer x = 1 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => 2 * y - y * y) (2 * (1 - x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa [mul_one] using (hasDerivAt_id x).const_mul 2
    have h2 : HasDerivAt (fun y : ℝ => y * y) (x + x) x := by
      have := hasDerivAt_pow 2 x
      simpa [pow_two, two_mul] using this
    exact (h1.sub h2).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun x : ℝ => 2 * (1 - x)) volume (0 : ℝ) 1 :=
    (by fun_prop : Continuous fun x : ℝ => 2 * (1 - x)).intervalIntegrable _ _
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hmain
  have hval : (fun y : ℝ => 2 * y - y * y) 1 - (fun y : ℝ => 2 * y - y * y) 0 = 1 := by norm_num
  rw [hval] at hmain
  have hhalf : ∫ x in (0 : ℝ)..1, (1 - x) = 1 / 2 := by
    refine (eq_div_iff two_ne_zero).mpr ?_
    simpa [mul_comm] using hmain
  have heven : ∀ x : ℝ, triKer (-x) = triKer x := by
    intro x
    simp only [triKer, abs_neg]
  have hs := integral_symm_zero_one triKer continuous_triKer heven
  have h01 : ∫ x in (0 : ℝ)..1, triKer x = ∫ x in (0 : ℝ)..1, (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hmem : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    obtain ⟨h0, h1'⟩ := Set.mem_Icc.mp hmem
    show triKer x = 1 - x
    rw [triKer_of_abs_le_one (abs_le.mpr ⟨by linarith, h1'⟩), abs_of_nonneg h0]
  calc ∫ x in (-1 : ℝ)..1, triKer x = 2 * ∫ x in (0 : ℝ)..1, triKer x := hs
    _ = 2 * ∫ x in (0 : ℝ)..1, (1 - x) := by rw [h01]
    _ = 1 := by rw [hhalf]; norm_num

lemma integral_eq_intervalIntegral_of_support (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, x ∉ Set.Icc (-1 : ℝ) 1 → f x = 0) :
    ∫ x : ℝ, f x = ∫ x in (-1 : ℝ)..1, f x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-1 : ℝ) 1) hf]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]

lemma fourierCos_triKer_zero : fourierCos triKer 0 = 1 := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc (-1 : ℝ) 1 →
      triKer x * Real.cos ((2 * Real.pi * 0) * x) = 0 := by
    intro x hx
    rw [triKer_eq_zero_of_notMem_Icc hx, zero_mul]
  have hred := integral_eq_intervalIntegral_of_support
    (fun x : ℝ => triKer x * Real.cos ((2 * Real.pi * 0) * x)) hsupp
  calc fourierCos triKer 0
      = ∫ x : ℝ, triKer x * Real.cos ((2 * Real.pi * 0) * x) := rfl
    _ = ∫ x in (-1 : ℝ)..1, triKer x * Real.cos ((2 * Real.pi * 0) * x) := hred
    _ = ∫ x in (-1 : ℝ)..1, triKer x := by
        apply intervalIntegral.integral_congr
        intro x _
        simp
    _ = 1 := integral_triKer

lemma fourierCos_triKer_ne (u : ℝ) (hu : u ≠ 0) :
    fourierCos triKer u = (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcu : Real.pi * u ≠ 0 := mul_ne_zero hpi hu
  have hc : (2 : ℝ) * (Real.pi * u) ≠ 0 := mul_ne_zero two_ne_zero hcu
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc (-1 : ℝ) 1 →
      triKer x * Real.cos (((2 * Real.pi) * u) * x) = 0 := by
    intro x hx
    rw [triKer_eq_zero_of_notMem_Icc hx, zero_mul]
  have hred := integral_eq_intervalIntegral_of_support
    (fun x : ℝ => triKer x * Real.cos (((2 * Real.pi) * u) * x)) hsupp
  have hkey : (1 : ℝ) - Real.cos (2 * (Real.pi * u)) = 2 * Real.sin (Real.pi * u) ^ 2 := by
    have h := Real.sin_sq_eq_half_sub (Real.pi * u)
    linarith [h]
  calc fourierCos triKer u
      = ∫ x : ℝ, triKer x * Real.cos (((2 * Real.pi) * u) * x) := rfl
    _ = ∫ x in (-1 : ℝ)..1, triKer x * Real.cos (((2 * Real.pi) * u) * x) := hred
    _ = 2 * ((1 - Real.cos ((2 * Real.pi) * u)) / ((2 * Real.pi) * u) ^ 2) := by
        apply integral_triKer_mul_cos
        simpa using hc
    _ = (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 := by
        rw [show (1 - Real.cos ((2 * Real.pi) * u))
            = 1 - Real.cos (2 * (Real.pi * u)) by ring,
          hkey]
        field_simp

theorem fourierCos_triKer (u : ℝ) :
    fourierCos triKer u = if u = 0 then 1 else (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 := by
  by_cases hu : u = 0
  · subst hu
    simpa using fourierCos_triKer_zero
  · simp only [hu, if_false]
    exact fourierCos_triKer_ne u hu

end QRH
