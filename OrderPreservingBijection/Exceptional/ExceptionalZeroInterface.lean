import OrderPreservingBijection.Exceptional.ExceptionalDirichletZeroUniqueZeroFreeRegion

/-! 接口层：把搬运来的 Deuring–Heilbronn 型「例外零点唯一 + 无零点区域」主定理
挂到本工程命名，便于下游引用与审计。
来源：Alpöge–Claude 归档 `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/
ExceptionalDirichletZeroUniqueZeroFreeRegion.lean`（29 文件闭包，全量搬运）。
公理集：`[propext, Classical.choice, Quot.sound]`（实测 `#print axioms`，无 axiom、无 sorry）。 -/

namespace OrderPreservingBijection.ExceptionalZero

theorem dirichlet_exceptional_zero_unique_zero_free_region :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ →
      ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M →
        (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ),
          GlobalTheory.Lin.IsExc c₁ χ β →
          GlobalTheory.Lin.IsExc c₁ χ' β' →
          χ = χ' ∧ β = β') ∧
        (∀ (χ : DirichletCharacter ℂ M) (β : ℝ),
          GlobalTheory.Lin.IsExc c₁ χ β →
          χ ≠ 1 ∧ 7 / 8 ≤ β ∧ DirichletCharacter.LFunction χ β = 0 ∧
          GlobalTheory.Lin.ord χ (β : ℂ) = 1 ∧
          c / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧
        ∀ (χ : DirichletCharacter ℂ M) (ρ : ℂ), ρ.re < 1 →
          DirichletCharacter.LFunction χ ρ = 0 →
          (ρ.im = 0 ∧ GlobalTheory.Lin.IsExc c₁ χ ρ.re) ∨
            ρ.re ≤ 1 - c / Real.log (M * (|ρ.im| + 2)) :=
  GlobalTheory.ExceptionalPair.main

end OrderPreservingBijection.ExceptionalZero
