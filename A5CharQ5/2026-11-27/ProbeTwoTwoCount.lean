import A5CharQ5.A5Defs
import A5CharQ5.ConjClasses

-- (a) S₅ 层 {2,2} 类大小 = 15（120 / 8）
example : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}} = 15 := by
  have hrep : ((sG ^ 2 * tG : G).val : Equiv.Perm (Fin 5)).cycleType = {2,2} := by
    native_decide
  have h15 : Nat.card {h : Equiv.Perm (Fin 5) |
      IsConj ((sG ^ 2 * tG : G).val) h} = 15 := by
    rw [Equiv.Perm.card_isConj_eq, hrep]
    norm_num
  have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}}
      = {h : Equiv.Perm (Fin 5) | IsConj ((sG ^ 2 * tG : G).val) h} := by
    ext h
    simp only [Set.mem_ofPred_eq]
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hrep, eq_comm]
  rw [hset]
  exact h15

-- (b) A₅ 层 {2,2} 类大小 = 15（双换位全偶，A₅ 与 S₅ 一致）
example : Nat.card {g : ↥G | g.val.cycleType = {2,2}} = 15 := by
  have h15 : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}} = 15 := by
    have hrep : ((sG ^ 2 * tG : G).val : Equiv.Perm (Fin 5)).cycleType = {2,2} := by
      native_decide
    have h15' : Nat.card {h : Equiv.Perm (Fin 5) |
        IsConj ((sG ^ 2 * tG : G).val) h} = 15 := by
      rw [Equiv.Perm.card_isConj_eq, hrep]
      norm_num
    have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}}
        = {h : Equiv.Perm (Fin 5) | IsConj ((sG ^ 2 * tG : G).val) h} := by
      ext h
      simp only [Set.mem_ofPred_eq]
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hrep, eq_comm]
    rw [hset]
    exact h15'
  rw [← h15]
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun g : {g : ↥G | g.val.cycleType = {2,2}} =>
      (⟨g.val.val, g.2⟩ : {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}}))
    ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}} =>
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
