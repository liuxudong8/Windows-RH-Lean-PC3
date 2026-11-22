import A5CharQ5.A5Defs
import Mathlib.GroupTheory.GroupAction.Quotient

-- (D) A₅ 中共轭类 (sG 的类) 大小 = 12
example : Nat.card (ConjClasses.mk sG).carrier = 12 := by
  haveI : Fintype ↥G := Fintype.ofFinite _
  haveI : Fintype (ConjClasses.mk sG).carrier := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (ConjAct ↥G) sG) := Fintype.ofFinite _
  have hC : Nat.card (Subgroup.centralizer ({sG} : Set ↥G)) = 5 := by
    have heq : Subgroup.centralizer ({sG} : Set ↥G) = Subgroup.closure ({sG} : Set ↥G) := by
      symm
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.closure_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        change ∀ h ∈ ({sG} : Set ↥G), h * sG = sG * h
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
      · have hcl : Nat.card (Subgroup.closure ({sG} : Set ↥G)) = 5 := by
          rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, orderOf_sG]
        rw [hcl]
        have hinj : Function.Injective
            (fun x : Subgroup.centralizer ({sG} : Set ↥G) =>
              (⟨(x : ↥G).val, by
                change ∀ h ∈ ({sG.val} : Set (Equiv.Perm (Fin 5))),
                  h * (x : ↥G).val = (x : ↥G).val * h
                intro h hh
                rw [Set.mem_singleton_iff] at hh
                rw [hh]
                exact congrArg Subtype.val (x.2 sG (Set.mem_singleton sG))⟩ :
                Subgroup.centralizer ({sG.val} : Set (Equiv.Perm (Fin 5))))) := by
          intro a b hab
          have hv : (a : ↥G).val = (b : ↥G).val :=
            congrArg (fun y : Subgroup.centralizer ({sG.val} : Set (Equiv.Perm (Fin 5))) =>
              (y : Equiv.Perm (Fin 5))) hab
          apply Subtype.ext
          apply Subtype.ext
          exact hv
        calc Nat.card (Subgroup.centralizer ({sG} : Set ↥G))
            ≤ Nat.card (Subgroup.centralizer ({sG.val} : Set (Equiv.Perm (Fin 5)))) :=
              Nat.card_le_card_of_injective _ hinj
          _ = 5 := by
              rw [Equiv.Perm.nat_card_centralizer]
              have hc : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
              rw [hc]
              norm_num
    rw [heq]
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, orderOf_sG]
  have hS : Fintype.card (MulAction.stabilizer (ConjAct ↥G) sG) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    exact hC
  have hG : Fintype.card ↥G = 60 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_G
  have hcard : Fintype.card (ConjClasses.mk sG).carrier = 12 := by
    rw [ConjClasses.card_carrier]
    rw [hG]
    rw [hS]
  rw [Nat.card_eq_fintype_card]
  exact hcard
