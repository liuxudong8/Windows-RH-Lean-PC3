import A5CharQ5.A5Defs

-- (1) 任意 5-循环的阶 = 5
example (g : G) (hg : g.val.cycleType = {5}) : orderOf g = 5 := by
  have h1 : orderOf (g.val : Equiv.Perm (Fin 5)) = 5 := by
    rw [← Equiv.Perm.lcm_cycleType, hg]
    simp
  rw [← Subgroup.orderOf_coe]
  exact h1

-- (2) S₅ 层 5-循环的总数 = 24
example : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {5}} = 24 := by
  have h24 : Nat.card {h : Equiv.Perm (Fin 5) | IsConj (sG.val : Equiv.Perm (Fin 5)) h} = 24 := by
    rw [Equiv.Perm.card_isConj_eq]
    have hc : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
    rw [hc]
    norm_num
  have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {5}}
      = {h : Equiv.Perm (Fin 5) | IsConj (sG.val : Equiv.Perm (Fin 5)) h} := by
    ext h
    have hc : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
    simp only [Set.mem_ofPred_eq]
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hc, eq_comm]
  rw [hset]
  exact h24

-- (3) A₅ 层 5-循环的总数 = 24（5-循环全是偶置换，故 A₅ 与 S₅ 一致）
example : Nat.card {g : ↥G | g.val.cycleType = {5}} = 24 := by
  have h24 : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {5}} = 24 := by
    have h1 : Nat.card {h : Equiv.Perm (Fin 5) | IsConj (sG.val : Equiv.Perm (Fin 5)) h} = 24 := by
      rw [Equiv.Perm.card_isConj_eq]
      have hc : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
      rw [hc]
      norm_num
    have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {5}}
        = {h : Equiv.Perm (Fin 5) | IsConj (sG.val : Equiv.Perm (Fin 5)) h} := by
      ext h
      have hc : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
      simp only [Set.mem_ofPred_eq]
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hc, eq_comm]
    rw [hset]
    exact h1
  rw [← h24]
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun g : {g : ↥G | g.val.cycleType = {5}} =>
      (⟨g.val.val, g.2⟩ : {h : Equiv.Perm (Fin 5) | h.cycleType = {5}}))
    ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : {h : Equiv.Perm (Fin 5) | h.cycleType = {5}} =>
      (x : Equiv.Perm (Fin 5))) hab
  · intro h
    have hsgn : h.val.sign = 1 := by
      rw [Equiv.Perm.sign_of_cycleType]
      rw [h.2]
      decide
    have hmem : h.val ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hsgn
    refine ⟨⟨⟨h.val, hmem⟩, h.2⟩, ?_⟩
    rfl
