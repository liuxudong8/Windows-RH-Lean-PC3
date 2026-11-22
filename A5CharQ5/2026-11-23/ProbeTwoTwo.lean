import A5CharQ5.A5Defs

/-- 对合 σ 与 `swap a (σ a)` 交换（(a, σa) 是 σ 的一个 2-循环）。 -/
theorem swap_commute_involution (σ : Equiv.Perm (Fin 5)) (hσ : σ ^ 2 = 1) (a : Fin 5)
    (ha : σ a ≠ a) :
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

set_option maxHeartbeats 500000 in
/-- **{2,2} 类共轭**：所有双换位在 A₅ 中共轭于 `sG²·tG`。
    走 S₅ 共轭 + 奇置换修正：若 π 是奇置换，乘上 support 内的 `swap a (σ a)`
    （它与 σ 交换）即可把 π 变偶，而共轭关系不变。 -/
theorem G_twoTwo_isConj (g : G) (h : g.val.cycleType = {2, 2}) :
    IsConj g (sG ^ 2 * tG : G) := by
  have h2 : (g.val : Equiv.Perm (Fin 5)) ^ 2 = 1 := by
    have hord : orderOf (g.val : Equiv.Perm (Fin 5)) = 2 := by
      rw [← Equiv.Perm.lcm_cycleType, h]
      simp
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hne : (g.val : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro hg
    have hz : (g.val : Equiv.Perm (Fin 5)).cycleType = 0 := by
      rw [hg]; exact Equiv.Perm.cycleType_one
    rw [hz] at h
    simp at h
  have hrep : ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)).cycleType = {2, 2} := by native_decide
  have hc : IsConj (g.val : Equiv.Perm (Fin 5)) ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)) := by
    apply Equiv.Perm.isConj_of_cycleType_eq
    rw [h, hrep]
  obtain ⟨πu, hπ⟩ := hc
  have hπ' : (↑πu : Equiv.Perm (Fin 5)) * (↑g : Equiv.Perm (Fin 5))
      = ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)) * (↑πu : Equiv.Perm (Fin 5)) := hπ
  rcases Int.units_eq_one_or (Equiv.Perm.sign (↑πu : Equiv.Perm (Fin 5))) with hs | hs
  · have hmem : (↑πu : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hs
    refine isConj_iff.2 ⟨⟨↑πu, hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : (↑πu : Equiv.Perm (Fin 5)) * (↑g : Equiv.Perm (Fin 5)) * (↑πu : Equiv.Perm (Fin 5))⁻¹
        = ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)) := by
      rw [hπ']
      rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [key]
    simp only [Subgroup.coe_mul]
  · obtain ⟨a, ha⟩ : ∃ a : Fin 5, (g.val : Equiv.Perm (Fin 5)) a ≠ a := by
      by_contra hall
      push_neg at hall
      exact hne (Equiv.ext hall)
    have hsne : a ≠ (g.val : Equiv.Perm (Fin 5)) a := fun hh => ha hh.symm
    have hcomm : Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a) * (g.val : Equiv.Perm (Fin 5))
        = (g.val : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a) :=
      swap_commute_involution g.val h2 a ha
    have hsign : Equiv.Perm.sign ((↑πu : Equiv.Perm (Fin 5))
        * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a)) = 1 := by
      rw [Equiv.Perm.sign_mul, hs, Equiv.Perm.sign_swap hsne, Int.units_mul_self]
    have hmem : ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))
        ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hsign
    refine isConj_iff.2 ⟨⟨(↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a),
      hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hcomm' : Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a) * (g.val : Equiv.Perm (Fin 5))
        * (Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))⁻¹ = (g.val : Equiv.Perm (Fin 5)) := by
      rw [hcomm]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have key : ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a)) * g.val
        * ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))⁻¹
        = ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)) := by
      have e1 : ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a)) * g.val
          * ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))⁻¹
          = (↑πu : Equiv.Perm (Fin 5))
            * (Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a) * g.val
              * (Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))⁻¹)
            * (↑πu : Equiv.Perm (Fin 5))⁻¹ := by
        rw [mul_inv_rev]
        simp only [mul_assoc]
      rw [e1]
      rw [hcomm']
      rw [hπ']
      rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [key]
    simp only [Subgroup.coe_mul]



