import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

#check div_le_iff₀
#check le_div_iff₀
#check abs_of_nonneg
#check le_abs_self
#check mul_le_mul_of_nonneg_left
#check Nat.cast_nonneg
#check Nat.lt_succ_iff
#check mul_nonneg

example : (857 : ℝ) / 1000 / (759291598 / 10^9) < 4 := by
  norm_num

example (n : ℕ) : (n : ℝ) < 4 → n ≤ 3 := by
  intro h
  exact Nat.lt_succ_iff.mp (by exact_mod_cast h)

example (a b c : ℝ) (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  exact div_le_iff₀ hc
