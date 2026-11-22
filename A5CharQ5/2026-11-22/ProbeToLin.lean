import A5CharQ5.A5Defs
import A5CharQ5.ConjClasses

-- C 路线：toLin' S ^ 4 = toLin' (S^4)
example : (Matrix.toLin' (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)) ^ 4
    = Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 4) := by
  rw [show (4 : ℕ) = 2 + 2 from by norm_num]
  rw [pow_add]
  rw [pow_two]
  rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ (2 + 2)
      = (icosahedralS ^ 2) * (icosahedralS ^ 2) from by rw [pow_add]]
  rw [Matrix.toLin'_mul]
  rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 2
      = icosahedralS * icosahedralS from pow_two (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)]
  rw [Matrix.toLin'_mul]
  rfl
