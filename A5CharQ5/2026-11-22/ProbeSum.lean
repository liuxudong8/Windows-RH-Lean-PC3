import A5CharQ5.A5Defs
import A5CharQ5.ConjClasses

-- 取逆保持共轭
theorem IsConj_inv {g h : ↥G} (hh : IsConj g h) : IsConj (g⁻¹) (h⁻¹) := by
  obtain ⟨c, hc⟩ := hh
  refine IsConj.symm ⟨c⁻¹, ?_⟩
  show ((c⁻¹ : (↥G)ˣ) : ↥G) * h⁻¹ = g⁻¹ * ((c⁻¹ : (↥G)ˣ) : ↥G)
  have hkey : ((↑c : ↥G))⁻¹ * h⁻¹ = g⁻¹ * ((↑c : ↥G))⁻¹ := by
    calc ((↑c : ↥G))⁻¹ * h⁻¹ = (h * (↑c : ↥G))⁻¹ := by rw [← mul_inv_rev]
      _ = ((↑c : ↥G) * g)⁻¹ := by rw [← hc]
      _ = g⁻¹ * ((↑c : ↥G))⁻¹ := by rw [mul_inv_rev]
  simpa [Units.val_inv_eq_inv_val] using hkey

-- χ(sG³) = α（tr(S³) = 1 + 2cos(2π/5) = α）
theorem char_sG_cube : icosahedralRep.character (sG ^ 3) = alpha := by
  calc
    icosahedralRep.character (sG ^ 3) =
        LinearMap.trace ℂ (Fin 3 → ℂ) (ρG (sG ^ 3)) := by
      rw [icosahedralRep, FDRep.character, FDRep.of_ρ']
    _ = LinearMap.trace ℂ (Fin 3 → ℂ) (ρP (pA ^ 3)) := by
      congr 1
      calc
        ρG (sG ^ 3) = ρP (ψ (sG ^ 3)) := by simp [ρG]
        _ = ρP ((ψ sG) ^ 3) := by rw [map_pow]
        _ = ρP (pA ^ 3) := by rw [psi_sG]
    _ = ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 3).trace := by
      have hto : (Matrix.toLin' (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)) ^ 3
          = Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 3) := by
        rw [pow_succ]
        rw [pow_two]
        rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 3
            = (icosahedralS ^ 2) * icosahedralS from by rw [pow_succ]]
        rw [Matrix.toLin'_mul]
        rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 2
            = icosahedralS * icosahedralS from
              pow_two (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)]
        rw [Matrix.toLin'_mul]
        rfl
      rw [show ρP (pA ^ 3) =
          Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 3) from by
        rw [map_pow, ρP_pA_eq]
        rw [hto]]
      exact Matrix.trace_toLin'_eq _
    _ = alpha := by
      rw [pow_succ]
      rw [pow_two]
      unfold Matrix.trace
      simp [Matrix.mul_apply, Fin.sum_univ_succ, icosahedralS, c5, g5]
      unfold alpha
      ring_nf
      norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four]
      ring_nf
