import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

example {m : ℕ} (hge : 2 ≤ m) : 4 ≤ m ^ 2 := by
  have hmul : 2 * 2 ≤ m * m := Nat.mul_le_mul hge hge
  calc
    4 = 2 * 2 := by norm_num
    _ ≤ m * m := hmul
    _ = m ^ 2 := by ring

example (h : (4 : ℕ) ≤ 3) : False := by
  norm_num at h
  exact h

example (hm : m = 0) (h : 1 ≤ m ^ 2) : False := by
  rw [hm] at h
  norm_num at h
  exact h

example : 1 ^ 2 = (1 : ℕ) := by norm_num
