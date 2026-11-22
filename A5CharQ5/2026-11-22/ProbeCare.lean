import A5CharQ5.A5Defs

example : ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)).cycleType = {2, 2} := by native_decide

example : alternatingGroup (Fin 5) = alternatingGroup (Fin 5) := rfl

example (σ : Equiv.Perm (Fin 5)) (hσ : σ ^ 2 = 1) (a : Fin 5) (ha : σ a ≠ a) :
    Equiv.swap a (σ a) * σ = σ * Equiv.swap a (σ a) := by
  have hsq : ∀ x, σ (σ x) = x := by
    intro x
    have h := congrArg (fun f : Equiv.Perm (Fin 5) => f x) hσ
    simpa [pow_two, Equiv.Perm.mul_apply] using h
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases h1 : x = a
  · rw [h1]
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left, hsq a]
  · by_cases h2 : x = σ a
    · rw [h2]
      rw [hsq a, Equiv.swap_apply_left, Equiv.swap_apply_right]
    · have h3 : σ x ≠ a := by
        intro hh
        apply h2
        rw [← hsq x, hh]
      have h4 : σ x ≠ σ a := by
        intro hh
        exact h1 (σ.injective hh)
      rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]
