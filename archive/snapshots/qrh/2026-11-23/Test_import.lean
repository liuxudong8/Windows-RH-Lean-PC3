import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

open Real
open Set
open Filter

-- 1. cos - 1 的导数（simpa 模式）
example {x : ℝ} : HasDerivAt (fun t : ℝ => cos t - 1) (-sin x) x := by
  simpa [sub_zero] using (Real.hasDerivAt_cos x).sub (hasDerivAt_const x 1)

-- 2. sin - id 的导数
example {x : ℝ} : HasDerivAt (fun u : ℝ => sin u - u) (cos x - 1) x := by
  simpa using (Real.hasDerivAt_sin x).sub (hasDerivAt_id x)

-- 3. u*cos u 的导数
example {x : ℝ} : HasDerivAt (fun u : ℝ => u * cos u) (cos x - x * sin x) x := by
  simpa [sub_eq_add_neg] using (hasDerivAt_id x).mul (Real.hasDerivAt_cos x)

-- 4. hlin：2π·t 的导数
example {u : ℝ} : HasDerivAt (fun t : ℝ => (2 * Real.pi) * t) (2 * Real.pi) u := by
  simpa [zero_mul, one_mul, zero_add] using
    (hasDerivAt_const u (2 * Real.pi)).mul (hasDerivAt_id u)

-- 5. Convex.norm_image_sub_le_of_norm_deriv_le 命名实参
example (x y : ℝ) (hdiff : ∀ x : ℝ, DifferentiableAt ℝ (fun t : ℝ => t) x)
    (hb : ∀ x : ℝ, ‖deriv (fun t : ℝ => t) x‖ ≤ (1 : ℝ) / 4) :
    |(fun t : ℝ => t) x - (fun t : ℝ => t) y| ≤ (1 : ℝ) / 4 * |x - y| := by
  have hres := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℝ)
    (f := fun t : ℝ => t) (s := Set.univ) (C := (1 : ℝ) / 4) (x := x) (y := y)
    (fun x _ => hdiff x) (fun x _ => hb x) convex_univ trivial trivial
  simpa [Real.norm_eq_abs] using hres

-- 6. div 导数域等式：f'/c = (f'c − f·0)/c²
example {c f' : ℝ} (hc : c ≠ 0) : f' / c = (f' * c - 0) / c ^ 2 := by
  field_simp [hc]
  ring
