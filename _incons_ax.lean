import QRH.S7_1_Core
import QRH.S7_1_Main

/-!
# 一致性探针：`fourierCos_Khat` 与 `bgs5_khat_fourier_supp` 互相矛盾

两条 axiom（均在账上、均被下游使用）：

* `fourierCos_Khat u : fourierCos Khat u = Khat u`（`S7_1_Core:705`）
* `bgs5_khat_fourier_supp u (h : 1 < |u|) : fourierCos Khat u = 0`（`S7_1_Main:375`）

合起来 ⟹ `∀ u, 1 < |u| → Khat u = 0`。但 `Khat` 是 sinc 梳状函数，
在 `u = 4/3`（`|u| > 1`）处 `Khat (4/3) < 0`（下面真证，只用符号判断）。
故这两条 axiom 同时成立即推出 `False`：**本开发的形式层是平凡的**。
-/

open QRH

/-- 合成推论：两条 axiom ⟹ `Khat` 在 `|u| > 1` 上恒零。 -/
theorem khat_eq_zero_of_one_lt_abs (u : ℝ) (h : 1 < |u|) : QRH.Khat u = 0 := by
  rw [← QRH.fourierCos_Khat u]
  exact QRH.bgs5_khat_fourier_supp u h

/-- `Khat (1/2) > 0`（备查：Khat 在 `|u| ≤ 1` 内非零）。 -/
theorem khat_half_pos : 0 < QRH.Khat (1 / 2) := by
  have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_lt : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hsq : Real.sqrt 2 < (1.42 : ℝ) := by
    have h2 : (2 : ℝ) < (1.42 : ℝ) ^ 2 := by norm_num
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.42)).mpr h2
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ha_neg : Real.sqrt 2 - Real.pi < 0 := by linarith
  have ha_bound : -(Real.pi) < (Real.sqrt 2 - Real.pi) / 2 := by linarith
  have hb_pos : 0 < Real.sqrt 2 + Real.pi := by linarith
  have hb_bound : (Real.sqrt 2 + Real.pi) / 2 < Real.pi := by linarith
  have hone : 0 < Real.sin ((Real.sqrt 2 - Real.pi) / 2) / (Real.sqrt 2 - Real.pi) := by
    have hs : Real.sin ((Real.sqrt 2 - Real.pi) / 2) < 0 := by
      apply Real.sin_neg_of_neg_of_neg_pi_lt
      · linarith
      · exact ha_bound
    exact div_pos_of_neg_of_neg hs ha_neg
  have htwo : 0 < Real.sin ((Real.sqrt 2 + Real.pi) / 2) / (Real.sqrt 2 + Real.pi) := by
    have hs : 0 < Real.sin ((Real.sqrt 2 + Real.pi) / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · exact hb_bound
    exact div_pos hs hb_pos
  have hden : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := by
    have hone_lt : (1 : ℝ) < Real.sqrt 2 := by
      have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      simpa using h
    have hsin : 0 < Real.sin (1 / Real.sqrt 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · have : (1 : ℝ) / Real.sqrt 2 < 1 := by
          rw [div_lt_one hsqrt_pos]
          exact hone_lt
        linarith [Real.pi_gt_three]
    exact mul_pos hsqrt_pos hsin
  unfold QRH.Khat QRH.S_smooth
  rw [show Real.sqrt 2 - 2 * Real.pi * (1 / 2) = Real.sqrt 2 - Real.pi by ring,
      show Real.sqrt 2 + 2 * Real.pi * (1 / 2) = Real.sqrt 2 + Real.pi by ring]
  rw [if_neg (ne_of_lt ha_neg), if_neg (ne_of_gt hb_pos)]
  exact div_pos (add_pos hone htwo) hden

/-- `Khat (4/3) < 0`（`|4/3| > 1`）：两项同为负。 -/
theorem khat_four_thirds_neg : QRH.Khat (4 / 3) < 0 := by
  have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_lt : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hsq_lt : Real.sqrt 2 < (1.42 : ℝ) := by
    have h2 : (2 : ℝ) < (1.42 : ℝ) ^ 2 := by norm_num
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.42)).mpr h2
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- a = √2 − 2π·(4/3) = √2 − 8π/3
  have ha_neg : Real.sqrt 2 - 2 * Real.pi * (4 / 3) < 0 := by
    nlinarith [hsq_lt, hpi_gt]
  -- a/2 = √2/2 − 4π/3 ∈ (−2π, −π)
  have ha_lo : -(2 * Real.pi) < (Real.sqrt 2 - 2 * Real.pi * (4 / 3)) / 2 := by
    nlinarith [hsqrt_pos, hpi_gt]
  have ha_hi : (Real.sqrt 2 - 2 * Real.pi * (4 / 3)) / 2 < -Real.pi := by
    nlinarith [hsq_lt, hpi_gt]
  -- sin(a/2) = sin(a/2 + 2π)，而 a/2 + 2π = √2/2 + 2π/3 ∈ (0, π)
  have hsa : 0 < Real.sin ((Real.sqrt 2 - 2 * Real.pi * (4 / 3)) / 2) := by
    rw [← Real.sin_add_two_pi ((Real.sqrt 2 - 2 * Real.pi * (4 / 3)) / 2)]
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [hsqrt_pos, hpi_gt]
    · nlinarith [hsq_lt, hpi_gt]
  -- b = √2 + 8π/3 > 0，b/2 = √2/2 + 4π/3 ∈ (π, 2π)
  have hb_pos : 0 < Real.sqrt 2 + 2 * Real.pi * (4 / 3) := by
    nlinarith [hsqrt_pos, hpi_gt]
  have hb_lo : Real.pi < (Real.sqrt 2 + 2 * Real.pi * (4 / 3)) / 2 := by
    nlinarith [hsqrt_pos, hpi_gt]
  have hb_hi : (Real.sqrt 2 + 2 * Real.pi * (4 / 3)) / 2 < 2 * Real.pi := by
    nlinarith [hsq_lt, hpi_gt]
  -- sin(b/2) = sin(b/2 − 2π)，而 b/2 − 2π = √2/2 − 2π/3 ∈ (−π, 0)
  have hsb : Real.sin ((Real.sqrt 2 + 2 * Real.pi * (4 / 3)) / 2) < 0 := by
    rw [← Real.sin_sub_two_pi ((Real.sqrt 2 + 2 * Real.pi * (4 / 3)) / 2)]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [hsq_lt, hpi_gt]
    · nlinarith [hsqrt_pos, hpi_gt]
  -- 分母 √2 · sin(1/√2) > 0
  have hone_lt : (1 : ℝ) < Real.sqrt 2 := by
    have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h
  have hden : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := by
    have hsin : 0 < Real.sin (1 / Real.sqrt 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · have : (1 : ℝ) / Real.sqrt 2 < 1 := by
          rw [div_lt_one hsqrt_pos]
          exact hone_lt
        linarith [Real.pi_gt_three]
    exact mul_pos hsqrt_pos hsin
  -- 两项各为负 ⟹ 和为负 ⟹ 商为负
  have ht1 : Real.sin ((Real.sqrt 2 - 2 * Real.pi * (4 / 3)) / 2)
      / (Real.sqrt 2 - 2 * Real.pi * (4 / 3)) < 0 :=
    div_neg_of_pos_of_neg hsa ha_neg
  have ht2 : Real.sin ((Real.sqrt 2 + 2 * Real.pi * (4 / 3)) / 2)
      / (Real.sqrt 2 + 2 * Real.pi * (4 / 3)) < 0 :=
    div_neg_of_neg_of_pos hsb hb_pos
  unfold QRH.Khat QRH.S_smooth
  rw [show Real.sqrt 2 - 2 * Real.pi * (4 / 3) = Real.sqrt 2 - 2 * Real.pi * (4 / 3) by ring,
      show Real.sqrt 2 + 2 * Real.pi * (4 / 3) = Real.sqrt 2 + 2 * Real.pi * (4 / 3) by ring]
  rw [if_neg (ne_of_lt ha_neg),
      if_neg (ne_of_gt hb_pos)]
  exact div_neg_of_neg_of_pos (add_neg ht1 ht2) hden

/-- **本开发的形式层不一致（机检）**：上述两条 axiom 一起推出 `False`。 -/
theorem qrh_axioms_inconsistent : False := by
  have hpos : QRH.Khat (4 / 3) < 0 := khat_four_thirds_neg
  have hzero : QRH.Khat (4 / 3) = 0 :=
    khat_eq_zero_of_one_lt_abs (4 / 3) (by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
      norm_num)
  linarith

#print axioms qrh_axioms_inconsistent
#print axioms khat_four_thirds_neg
