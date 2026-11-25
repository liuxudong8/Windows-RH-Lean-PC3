import QRH.S7_1_Main

example (N : ℕ) (h : 1 ≤ N) :
    (∑ _n ∈ Finset.Icc 1 N, (Real.log (N : ℝ)) : ℝ) = (N : ℝ) * Real.log (N : ℝ) := by
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp
