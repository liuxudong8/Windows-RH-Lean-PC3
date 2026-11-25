import A5CharQ5.A5Defs
import A5CharQ5.ConjClasses
import Mathlib.GroupTheory.GroupAction.ConjAct

-- (1) 任意 5-循环的中心化子 = ⟨g⟩
theorem t1 (g : G) (hg : g.val.cycleType = {5}) :
    Subgroup.centralizer ({g} : Set ↥G) = Subgroup.closure ({g} : Set ↥G) := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge
    (H := Subgroup.closure ({g} : Set ↥G))
    (K := Subgroup.centralizer ({g} : Set ↥G))
  · rw [Subgroup.closure_le]
    intro y hy
    rw [hy]
    change ∀ h ∈ ({g} : Set ↥G), h * g = g * h
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  · have hcl : Nat.card (Subgroup.closure ({g} : Set ↥G)) = 5 := by
      rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
      exact G_fiveCycle_orderOf g hg
    rw [hcl]
    let φ : Subgroup.centralizer ({g} : Set ↥G) →
        Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin 5))) :=
      fun x => ⟨(x : ↥G).val, by
        change ∀ h ∈ ({g.val} : Set (Equiv.Perm (Fin 5))), h * (x : ↥G).val = (x : ↥G).val * h
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        simpa [Subgroup.coe_mul] using congrArg Subtype.val (x.2 g (Set.mem_singleton g))⟩
    have hinj : Function.Injective φ := by
      intro a b hab
      have hv : (a : ↥G).val = (b : ↥G).val :=
        congrArg (fun y : Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin 5))) =>
          (y : Equiv.Perm (Fin 5))) hab
      apply Subtype.ext
      apply Subtype.ext
      exact hv
    calc Nat.card (Subgroup.centralizer ({g} : Set ↥G))
        ≤ Nat.card (Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin 5)))) :=
          Nat.card_le_card_of_injective _ hinj
      _ = 5 := by
          rw [Equiv.Perm.nat_card_centralizer, hg]
          norm_num

-- (2) 任意 5-循环的类大小 = 12
theorem t2 (g : G) (hg : g.val.cycleType = {5}) :
    Nat.card (ConjClasses.mk g).carrier = 12 := by
  haveI : Fintype ↥G := Fintype.ofFinite _
  haveI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (ConjAct ↥G) g) := Fintype.ofFinite _
  have hS : Fintype.card (MulAction.stabilizer (ConjAct ↥G) g) = 5 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    rw [t1 g hg]
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, G_fiveCycle_orderOf g hg]
  have hG : Fintype.card ↥G = 60 := by
    rw [← Nat.card_eq_fintype_card]; exact card_G
  have hcard : Fintype.card (ConjClasses.mk g).carrier = 12 := by
    rw [ConjClasses.card_carrier]; rw [hG]; rw [hS]
  rw [Nat.card_eq_fintype_card]
  exact hcard

-- (3) 类集合的基数 = 12
theorem t3 (g : G) (hg : g.val.cycleType = {5}) :
    Nat.card {h : ↥G | IsConj g h} = 12 := by
  have hset : ({h : ↥G | IsConj g h} : Set ↥G) = (ConjClasses.mk g).carrier := by
    ext h
    simp only [Set.mem_ofPred_eq]
    rw [← ConjAct.orbit_eq_carrier_conjClasses g]
    rw [ConjAct.mem_orbit_conjAct]
    exact isConj_comm
  rw [hset]
  exact t2 g hg
-- (4) {5} 类析取：任意 5-循环 与 sG 或 sG² 共轭
theorem t4 (g : G) (hg : g.val.cycleType = {5}) :
    IsConj g sG ∨ IsConj g (sG ^ 2) := by
  have hsg : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
  have hsg2 : (sG ^ 2 : G).val.cycleType = {5} := by native_decide
  have hA : Nat.card ({h : ↥G | IsConj sG h} : Set ↥G) = 12 := t3 sG hsg
  have hB : Nat.card ({h : ↥G | IsConj (sG ^ 2) h} : Set ↥G) = 12 := t3 (sG ^ 2) hsg2
  have hdisj : Disjoint ({h : ↥G | IsConj sG h} : Set ↥G)
      ({h : ↥G | IsConj (sG ^ 2) h} : Set ↥G) := by
    rw [Set.disjoint_left]
    intro h h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    exact sG_not_isConj_sG_sq (IsConj.trans h1 (IsConj.symm h2))
  have hEq : ({h : ↥G | h.val.cycleType = {5}} : Set ↥G)
      = {h : ↥G | IsConj sG h} ∪ {h : ↥G | IsConj (sG ^ 2) h} := by
    apply Eq.symm
    apply Set.eq_of_subset_of_ncard_le (ht := by exact Set.toFinite _)
    · intro h hh
      rw [Set.mem_union] at hh
      rcases hh with h1 | h1
      · simp only [Set.mem_ofPred_eq] at h1 ⊢
        obtain ⟨c, hc⟩ := h1
        have hv : IsConj (sG.val : Equiv.Perm (Fin 5)) h.val := by
          refine ⟨Units.map (Subgroup.subtype (alternatingGroup (Fin 5))) c, ?_⟩
          simpa [SemiconjBy, Subgroup.coe_mul, Units.coe_map] using congrArg Subtype.val hc
        rw [Equiv.Perm.isConj_iff_cycleType_eq] at hv
        rw [← hv, hsg]
      · simp only [Set.mem_ofPred_eq] at h1 ⊢
        obtain ⟨c, hc⟩ := h1
        have hv : IsConj ((sG ^ 2 : G).val : Equiv.Perm (Fin 5)) h.val := by
          refine ⟨Units.map (Subgroup.subtype (alternatingGroup (Fin 5))) c, ?_⟩
          simpa [SemiconjBy, Subgroup.coe_mul, Units.coe_map] using congrArg Subtype.val hc
        rw [Equiv.Perm.isConj_iff_cycleType_eq] at hv
        rw [← hv, hsg2]
    · rw [Set.ncard_union_eq hdisj (ht := by exact Set.toFinite _)]
      rw [show ({h : ↥G | IsConj sG h} : Set ↥G).ncard = 12 from
        (Nat.card_coe_set_eq _).symm.trans hA]
      rw [show ({h : ↥G | IsConj (sG ^ 2) h} : Set ↥G).ncard = 12 from
        (Nat.card_coe_set_eq _).symm.trans hB]
      rw [show ({h : ↥G | h.val.cycleType = {5}} : Set ↥G).ncard = 24 from
        (Nat.card_coe_set_eq _).symm.trans G_fiveCycle_count]
  have hgmem : g ∈ ({h : ↥G | h.val.cycleType = {5}} : Set ↥G) := hg
  rw [hEq] at hgmem
  rw [Set.mem_union] at hgmem
  rcases hgmem with h1 | h1
  · simp only [Set.mem_ofPred_eq] at h1
    exact Or.inl (IsConj.symm h1)
  · simp only [Set.mem_ofPred_eq] at h1
    exact Or.inr (IsConj.symm h1)
