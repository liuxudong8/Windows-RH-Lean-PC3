import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Group.Indicator

-- 探针 A：Real.norm_eq_abs 的 rw 是否展开 ‖C*b‖
example (C b : ℝ) (h : 0 ≤ C * b) : ‖C * b‖ = C * b := by
  rw [Real.norm_eq_abs]
  exact abs_of_nonneg h

-- 探针 B：| |a| | = |a|（abs_abs）
example (a : ℝ) : ‖|a|‖ = |a| := by
  rw [Real.norm_eq_abs, abs_abs]

-- 探针 C：indicator_of_mem 需显式 f
example (I : Set ℝ) (x : ℝ) (hx : x ∈ I) :
    (fun _ : ℝ => (1 : ℝ)) x = I.indicator (fun _ : ℝ => (1 : ℝ)) x := by
  exact (Set.indicator_of_mem (f := fun _ : ℝ => (1 : ℝ)) hx).symm

-- 探针 D：norm 包 abs 的单调目标（完整形态）
example (f g : ℝ → ℝ) (x : ℝ) (hf : Measurable f) (hg : Measurable g) :
    ‖|f x - g x|‖ ≤ ‖f x * (1 - g x)‖ := by
  have hpoint : |f x - g x| ≤ f x * (1 - g x) := by sorry
  calc
    ‖|f x - g x|‖ = |f x - g x| := by rw [Real.norm_eq_abs, abs_abs]
    _ ≤ f x * (1 - g x) := hpoint
