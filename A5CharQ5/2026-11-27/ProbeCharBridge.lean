import A5CharQ5.A5Defs
import A5CharQ5.ConjClasses

-- (1) χ(sG⁻¹) = ᾱ
theorem char_sG_inv : icosahedralRep.character (sG⁻¹) = 1 - alpha := by
  have h5 : sG ^ 5 = 1 := by
    have := pow_orderOf_eq_one sG
    rwa [orderOf_sG] at this
  have hinv : sG⁻¹ = sG ^ 4 := by
    have h4 : sG ^ 4 * sG = 1 := by
      rw [← pow_succ, h5]
    exact inv_eq_of_mul_eq_one_left h4
  calc
    icosahedralRep.character (sG⁻¹) =
        LinearMap.trace ℂ (Fin 3 → ℂ) (ρG (sG⁻¹)) := by
      rw [icosahedralRep, FDRep.character, FDRep.of_ρ']
    _ = LinearMap.trace ℂ (Fin 3 → ℂ) (ρP (pA ^ 4)) := by
      congr 1
      calc
        ρG (sG⁻¹) = ρG (sG ^ 4) := by rw [hinv]
        _ = ρP (ψ (sG ^ 4)) := by simp [ρG]
        _ = ρP ((ψ sG) ^ 4) := by rw [map_pow]
        _ = ρP (pA ^ 4) := by rw [psi_sG]
    _ = (icosahedralS ^ 4).trace := by
      have hto : (Matrix.toLin' (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)) ^ 4
          = Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 4) := by
        rw [show (4 : ℕ) = 2 + 2 from by norm_num]
        rw [pow_add]
        rw [pow_two]
        rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ (2 + 2)
            = (icosahedralS ^ 2) * (icosahedralS ^ 2) from by rw [pow_add]]
        rw [Matrix.toLin'_mul]
        rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 2
            = icosahedralS * icosahedralS from
              pow_two (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)]
        rw [Matrix.toLin'_mul]
        rfl
      rw [show ρP (pA ^ 4) =
          Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 4) from by
        rw [map_pow, ρP_pA_eq]
        rw [hto]]
      exact Matrix.trace_toLin'_eq _
    _ = 1 - alpha := by
      rw [show (4 : ℕ) = 2 + 2 from by norm_num, pow_add]
      rw [pow_two (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)]
      unfold Matrix.trace
      simp [Fin.sum_univ_succ, icosahedralS, c5, g5]
      unfold alpha
      ring_nf
      norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four]
      ring_nf

-- (2) IsConj 推 char 相等
theorem char_eq_of_isConj (g h : G) (hh : IsConj g h) :
    icosahedralRep.character h = icosahedralRep.character g := by
  obtain ⟨c, hc⟩ := hh
  have h1 : h * (↑c : ↥G) * (↑c : ↥G)⁻¹ = h := by
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have h2 : h * (↑c : ↥G) * (↑c : ↥G)⁻¹ = (↑c : ↥G) * g * (↑c : ↥G)⁻¹ := by
    rw [← hc]
  -- hc : (↑c) * g = h * (↑c)
  have hcy : h = (↑c : ↥G) * g * (↑c : ↥G)⁻¹ := h1.symm.trans h2
  rw [hcy]
  exact FDRep.char_conj icosahedralRep g (↑c)
