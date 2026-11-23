import QRH.S7_1_Core
import QRH.S7_1_Main

/-! 第七刀 A1+A2 探针：三角核 `triKer` 的四条基本面 + `prime_weight_bounds_tri`。 -/

open QRH

#print axioms triKer_zero
#print axioms triKer_supp
#print axioms triKer_abs_le_one
#print axioms triKer_lipschitz
#print axioms prime_weight_bounds_tri

/-- 定义即得的支撑性（原 `bgs5_khat_fourier_supp` 的替代物）。 -/
example (u : ℝ) (h : 1 < |u|) : triKer u = 0 := triKer_supp h

/-- 常数：M = δ + 1。 -/
example (δ : ℝ) (hδ : 0 < δ) : ∃ M : ℝ, 0 ≤ M ∧
    (∀ n : ℕ, 1 ≤ n →
      |(Real.sqrt (n : ℝ))⁻¹ * triKer (δ * Real.log (n : ℝ))| ≤ M * (Real.sqrt (n : ℝ))⁻¹) := by
  obtain ⟨M, hM, hb, hΔ⟩ := prime_weight_bounds_tri δ hδ
  exact ⟨M, hM, hb⟩
