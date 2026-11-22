import A5CharQ5.A5Defs

/-- cycleType 为空 ⟹ 元素是 1，故与 1 共轭。 -/
theorem G_cycleType_empty_isConj (g : G) (h : g.val.cycleType = 0) : IsConj g 1 := by
  have hv : g.val = 1 := Equiv.Perm.cycleType_eq_zero.mp h
  have hg : g = 1 := Subtype.ext hv
  subst hg
  exact ⟨1, by simp [SemiconjBy]⟩

/-- 所有 3-循环在 A₅ 中共轭（`IsThreeCycle` 就是 cycleType = {3}）。 -/
theorem G_threeCycle_isConj (g : G) (h : g.val.cycleType = {3}) : IsConj g tG := by
  have hrep : (tG : Equiv.Perm (Fin 5)).cycleType = {3} := by decide
  exact alternatingGroup.isThreeCycle_isConj (α := Fin 5) (by simp) h hrep
