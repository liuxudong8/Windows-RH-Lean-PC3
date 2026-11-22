import A5CharQ5.A5Defs
import A5CharQ5.ConjClasses

attribute [local instance] Classical.propDecidable

/-- 恒等元这一段：只有 1 个元素，取值 3·3 = 9。 -/
theorem sum_zero_class :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = 0))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹) = 9 := by
  have hS1 : Finset.univ.filter (fun g : ↥G => g.val.cycleType = 0) = {1} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro h
      have hg : g = 1 := by
        apply Subtype.ext
        simpa using (Equiv.Perm.cycleType_eq_zero.mp h)
      rw [hg]
    · rintro h
      rw [h]
      show ((1 : ↥G).val : Equiv.Perm (Fin 5)).cycleType = 0
      exact Equiv.Perm.cycleType_one
  rw [hS1, Finset.sum_singleton]
  rw [inv_one, char_one]
  norm_num

/-- {3} 这一段：χ 恒为 0，整段求和为 0。 -/
theorem sum_three_class :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {3}))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹) = 0 := by
  rw [Finset.sum_eq_zero]
  intro g hg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
  have hconj : IsConj g tG := G_threeCycle_isConj g hg
  have hchi : icosahedralRep.character g = 0 := by
    have h := char_eq_of_isConj tG g (IsConj.symm hconj)
    rwa [char_tG] at h
  rw [hchi, zero_mul]

/-- {2,2} 这一段：15 个元素，每个取值 (−1)·(−1) = 1。 -/
theorem sum_two_two_class :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {2, 2}))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹) = 15 := by
  have hc : ∀ g ∈ Finset.univ.filter (fun g : ↥G => g.val.cycleType = {2, 2}),
      icosahedralRep.character g * icosahedralRep.character g⁻¹ = 1 := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have hg2 : g ^ 2 = 1 := by
      have ho : orderOf (g.val : Equiv.Perm (Fin 5)) = 2 := by
        rw [← Equiv.Perm.lcm_cycleType, hg]
        simp
      have ho2 : orderOf g = 2 := by rwa [← Subgroup.orderOf_coe]
      rw [← ho2]
      exact pow_orderOf_eq_one g
    have hginv : g⁻¹ = g := by
      have h2 : g * g = 1 := by rw [← pow_two]; exact hg2
      exact inv_eq_of_mul_eq_one_left h2
    have hconj : IsConj g (sG ^ 2 * tG) := G_twoTwo_isConj g hg
    have hchi : icosahedralRep.character g = -1 := by
      have h := char_eq_of_isConj (sG ^ 2 * tG) g (IsConj.symm hconj)
      rwa [char_sG_sq_tG] at h
    rw [hginv, hchi]
    norm_num
  rw [Finset.sum_congr rfl hc, Finset.sum_const]
  have hcard :
      (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {2, 2})).card = 15 := by
    have h1 : Nat.card {g : ↥G | g.val.cycleType = {2, 2}} = 15 := G_twoTwo_set_card
    have h2 : Fintype.card {g : ↥G // g.val.cycleType = {2, 2}} = 15 := by
      rwa [Nat.card_eq_fintype_card] at h1
    rw [← Fintype.card_subtype]
    exact h2
  rw [hcard]
  norm_num

/-- 共轭保持 cycleType：A₅ 内共轭的两元素 cycleType 相同。 -/
theorem G_isConj_cycleType (g h : ↥G) (hh : IsConj g h) :
    h.val.cycleType = g.val.cycleType := by
  obtain ⟨c, hc⟩ := hh
  have hcy : h = (↑c : ↥G) * g * (↑c : ↥G)⁻¹ := by
    have h1 : h * (↑c : ↥G) * (↑c : ↥G)⁻¹ = h := by
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have h2 : h * (↑c : ↥G) * (↑c : ↥G)⁻¹ = (↑c : ↥G) * g * (↑c : ↥G)⁻¹ := by
      rw [← hc]
    exact h1.symm.trans h2
  have hperm : (h.val : Equiv.Perm (Fin 5))
      = ((↑c : ↥G).val) * g.val * ((↑c : ↥G).val)⁻¹ := by
    conv_lhs => rw [hcy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hperm, Equiv.Perm.cycleType_conj]

theorem sG_pow_eq_one : sG ^ 5 = 1 := by
  have := pow_orderOf_eq_one sG
  rwa [orderOf_sG] at this

theorem sG_inv_eq_pow_four : sG⁻¹ = sG ^ 4 := by
  have h4 : sG ^ 4 * sG = 1 := by rw [← pow_succ, sG_pow_eq_one]
  exact inv_eq_of_mul_eq_one_left h4

theorem sG_val_cycleType : sG.val.cycleType = {5} := by decide

/-- {5} 类 A 段（与 sG 共轭）：12 个，每项 ᾱ² = 2 − α。 -/
theorem sum_five_a :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹)
      = 12 * (2 - alpha) := by
  classical
  have hkey : (1 - alpha) * (1 - alpha) = 2 - alpha := by
    calc (1 - alpha) * (1 - alpha) = 1 - 2 * alpha + alpha * alpha := by ring
      _ = 1 - 2 * alpha + (1 + alpha) := by rw [alpha_sq]
      _ = 2 - alpha := by ring
  have hc : ∀ g ∈ Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG),
      icosahedralRep.character g * icosahedralRep.character g⁻¹ = 2 - alpha := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨_, hconj⟩ := hg
    have h1 : icosahedralRep.character g = 1 - alpha := by
      have h := char_eq_of_isConj sG g (IsConj.symm hconj)
      rwa [char_sG] at h
    have h2 : icosahedralRep.character g⁻¹ = 1 - alpha := by
      have hinv : IsConj (g⁻¹) (sG⁻¹) := IsConj_inv hconj
      have h := char_eq_of_isConj (sG⁻¹) (g⁻¹) (IsConj.symm hinv)
      rwa [char_sG_inv] at h
    rw [h1, h2, hkey]
  rw [Finset.sum_congr rfl hc, Finset.sum_const]
  have hcard :
      (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG)).card = 12 := by
    have hset : {g : ↥G | g.val.cycleType = {5} ∧ IsConj g sG} = {g : ↥G | IsConj sG g} := by
      ext g
      change (g.val.cycleType = {5} ∧ IsConj g sG) ↔ IsConj sG g
      constructor
      · rintro ⟨_, hc⟩
        exact IsConj.symm hc
      · intro hc
        have hg5 : g.val.cycleType = {5} := by
          rw [G_isConj_cycleType sG g hc, sG_val_cycleType]
        exact ⟨hg5, IsConj.symm hc⟩
    have h1 : Nat.card {g : ↥G | g.val.cycleType = {5} ∧ IsConj g sG} = 12 := by
      rw [hset]
      exact G_class_fiveCycle_set_card sG sG_val_cycleType
    have h2 : Fintype.card {g : ↥G // g.val.cycleType = {5} ∧ IsConj g sG} = 12 := by
      rwa [Nat.card_eq_fintype_card] at h1
    rw [← Fintype.card_subtype]
    exact h2
  rw [hcard]
  norm_num

theorem sG_sq_val_cycleType : ((sG ^ 2 : ↥G).val : Equiv.Perm (Fin 5)).cycleType = {5} := by
  native_decide

theorem sG_sq_inv_eq_cube : ((sG ^ 2 : ↥G))⁻¹ = sG ^ 3 := by
  rw [← inv_pow, sG_inv_eq_pow_four, ← pow_mul]
  rw [show (4 * 2 : ℕ) = 3 + 5 from by norm_num, pow_add, sG_pow_eq_one, mul_one]

/-- {5} 类 B 段（与 sG² 共轭）：12 个，每项 α² = 1 + α。 -/
theorem sum_five_b :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹)
      = 12 * (1 + alpha) := by
  classical
  have hc : ∀ g ∈ Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)),
      icosahedralRep.character g * icosahedralRep.character g⁻¹ = 1 + alpha := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨_, hconj⟩ := hg
    have h1 : icosahedralRep.character g = alpha := by
      have h := char_eq_of_isConj (sG ^ 2) g (IsConj.symm hconj)
      rwa [char_sG_sq] at h
    have h2 : icosahedralRep.character g⁻¹ = alpha := by
      have hinv : IsConj (g⁻¹) ((sG ^ 2)⁻¹) := IsConj_inv hconj
      rw [sG_sq_inv_eq_cube] at hinv
      have h := char_eq_of_isConj (sG ^ 3) (g⁻¹) (IsConj.symm hinv)
      rwa [char_sG_cube] at h
    rw [h1, h2, alpha_sq]
  rw [Finset.sum_congr rfl hc, Finset.sum_const]
  have hcard :
      (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2))).card = 12 := by
    have hset : {g : ↥G | g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)}
        = {g : ↥G | IsConj (sG ^ 2) g} := by
      ext g
      change (g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)) ↔ IsConj (sG ^ 2) g
      constructor
      · rintro ⟨_, hc⟩
        exact IsConj.symm hc
      · intro hc
        have hg5 : g.val.cycleType = {5} := by
          rw [G_isConj_cycleType (sG ^ 2) g hc, sG_sq_val_cycleType]
        exact ⟨hg5, IsConj.symm hc⟩
    have h1 : Nat.card {g : ↥G | g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)} = 12 := by
      rw [hset]
      exact G_class_fiveCycle_set_card (sG ^ 2) sG_sq_val_cycleType
    have h2 : Fintype.card {g : ↥G // g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)} = 12 := by
      rwa [Nat.card_eq_fintype_card] at h1
    rw [← Fintype.card_subtype]
    exact h2
  rw [hcard]
  ring
