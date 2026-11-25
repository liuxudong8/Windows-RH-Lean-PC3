import A5CharQ5.A5Defs
import A5CharQ5.ConjClasses

-- (a) S₅ 层 {3} 类大小 = 20（120 / 6）
example : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {3}} = 20 := by
  have hrep : (tG.val : Equiv.Perm (Fin 5)).cycleType = {3} := by decide
  have h20 : Nat.card {h : Equiv.Perm (Fin 5) | IsConj tG.val h} = 20 := by
    rw [Equiv.Perm.card_isConj_eq, hrep]
    norm_num
  have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {3}}
      = {h : Equiv.Perm (Fin 5) | IsConj tG.val h} := by
    ext h
    simp only [Set.mem_ofPred_eq]
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hrep, eq_comm]
  rw [hset]
  exact h20

-- (b) A₅ 层 {3} 类大小 = 20（3-循环全偶，A₅ 与 S₅ 一致）
example : Nat.card {g : ↥G | g.val.cycleType = {3}} = 20 := by
  have h20 : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {3}} = 20 := by
    have hrep : (tG.val : Equiv.Perm (Fin 5)).cycleType = {3} := by decide
    have h20' : Nat.card {h : Equiv.Perm (Fin 5) | IsConj tG.val h} = 20 := by
      rw [Equiv.Perm.card_isConj_eq, hrep]
      norm_num
    have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {3}}
        = {h : Equiv.Perm (Fin 5) | IsConj tG.val h} := by
      ext h
      simp only [Set.mem_ofPred_eq]
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hrep, eq_comm]
    rw [hset]
    exact h20'
  rw [← h20]
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun g : {g : ↥G | g.val.cycleType = {3}} =>
      (⟨g.val.val, g.2⟩ : {h : Equiv.Perm (Fin 5) | h.cycleType = {3}}))
    ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : {h : Equiv.Perm (Fin 5) | h.cycleType = {3}} =>
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
