import A5CharQ5.A5Defs

/-- α = (1+√5)/2 ≠ 1/2。 -/
lemma alpha_ne_half : alpha ≠ (1 / 2 : ℂ) := by
  intro h
  have hr : ((1 + Real.sqrt 5) / 2 : ℝ) = 1 / 2 := by
    have hre := congrArg Complex.re h
    simpa [alpha] using hre
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- **第 2 步核心**：5-循环在 A₅ 中双分裂 —— `sG` 与 `sG²` 不共轭。
    证明走特征标：共轭元上 χ 相同，而 χ(sG²)=α、χ(sG)=1-α，α≠1/2。 -/
theorem sG_not_isConj_sG_sq : ¬ IsConj (sG : G) (sG ^ 2) := by
  rintro ⟨c, hc⟩
  have hrel : (↑c : G) * sG * (↑c : G)⁻¹ = sG ^ 2 := by
    have hc' : (↑c : G) * sG = sG ^ 2 * (↑c : G) := hc
    rw [hc']
    group
  have hχ := FDRep.char_conj icosahedralRep sG (↑c : G)
  rw [hrel, char_sG_sq, char_sG] at hχ
  have h2 : 2 * alpha = 1 := by linear_combination hχ
  have ha : alpha = (1 / 2 : ℂ) := by
    rw [show (1 : ℂ) = 2 * (1 / 2 : ℂ) by norm_num] at h2
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2
  exact alpha_ne_half ha
