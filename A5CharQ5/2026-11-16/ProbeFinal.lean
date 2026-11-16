import A5CharQ5.ConjClasses

attribute [local instance] Classical.propDecidable

/-- **第 4 步（三）**：不可约判据的和 —— `∑ g, χ(g)χ(g⁻¹) = 60 = |A₅|`。

五段拆分：`{1}` 9、`{3}` 0、`{2,2}` 15、`{5}A` 12(2−α)、`{5}B` 12(1+α)，
合计 `24 + 12·3 = 60`。 -/
theorem icosahedral_char_sum :
    Finset.sum (Finset.univ : Finset ↥G)
      (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹) = 60 := by
  classical
  -- 逐层拆分：p1 = {1}、p2 = {3}、p3 = {2,2}、p4 = {5}A、p5 = {5}B
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ↥G)
    (fun g : ↥G => g.val.cycleType = 0)
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0))
    (fun g : ↥G => g.val.cycleType = {3})
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  rw [← Finset.sum_filter_add_sum_filter_not
    (((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3}))
    (fun g : ↥G => g.val.cycleType = {2, 2})
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2}))
    (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG)
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  rw [← Finset.sum_filter_add_sum_filter_not
    (((((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2})).filter
      (fun g : ↥G => ¬ (g.val.cycleType = {5} ∧ IsConj g sG)))
    (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2))
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  -- 桥接：累积 filter 化回裸 filter（`filter_filter` 右结合）
  have hb2 : (Finset.univ.filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => g.val.cycleType = {3})
      = Finset.univ.filter (fun g : ↥G => g.val.cycleType = {3}) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro h; exact h.2
    · intro h
      exact ⟨by rw [h]; decide, h⟩
  have hb3 : ((Finset.univ.filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => g.val.cycleType = {2, 2})
      = Finset.univ.filter (fun g : ↥G => g.val.cycleType = {2, 2}) := by
    rw [Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro h; exact h.2.2
    · intro h
      exact ⟨by rw [h]; decide, ⟨by rw [h]; decide, h⟩⟩
  have hb4 : (((Finset.univ.filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2})).filter
      (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG)
      = Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG) := by
    rw [Finset.filter_filter, Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro h; exact h.2.2.2
    · intro h
      exact ⟨by rw [h.1]; decide, ⟨by rw [h.1]; decide, ⟨by rw [h.1]; decide, h⟩⟩⟩
  have hb5 : ((((Finset.univ.filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2})).filter
      (fun g : ↥G => ¬ (g.val.cycleType = {5} ∧ IsConj g sG))).filter
      (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2))
      = Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)) := by
    rw [Finset.filter_filter, Finset.filter_filter, Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro h; exact h.2.2.2.2
    · intro h
      refine ⟨by rw [h.1]; decide, ⟨by rw [h.1]; decide,
        ⟨by rw [h.1]; decide, ⟨?_, h⟩⟩⟩⟩
      intro hh
      exact sG_not_isConj_sG_sq (IsConj.trans (IsConj.symm hh.2) h.2)
  -- 末段为空：五段已覆盖全部 60 元
  have hempty : (((((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2})).filter
      (fun g : ↥G => ¬ (g.val.cycleType = {5} ∧ IsConj g sG))).filter
      (fun g : ↥G => ¬ (g.val.cycleType = {5} ∧ IsConj g (sG ^ 2))) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have h1 : ¬ g.val.cycleType = 0 := hg.1.1.1.1
    have h2 : ¬ g.val.cycleType = {3} := hg.1.1.1.2
    have h3 : ¬ g.val.cycleType = {2, 2} := hg.1.1.2
    have h4 : ¬ (g.val.cycleType = {5} ∧ IsConj g sG) := hg.1.2
    have h5 : ¬ (g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)) := hg.2
    rcases G_cycleType_cases g with hc | hc | hc | hc
    · exact h1 hc
    · exact h2 hc
    · rcases G_fiveCycle_isConj_sG g hc with hcs | hcs
      · exact h4 ⟨hc, hcs⟩
      · exact h5 ⟨hc, hcs⟩
    · exact h3 hc
  rw [hb2, hb3, hb4, hb5, hempty, Finset.sum_empty]
  rw [sum_zero_class, sum_three_class, sum_two_two_class, sum_five_a, sum_five_b]
  ring
