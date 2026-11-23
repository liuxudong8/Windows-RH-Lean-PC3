import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic
import OrderPreservingBijection.Exceptional.ExistsDirichletLFunctionZeroGapNearOne
import OrderPreservingBijection.Exceptional.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ), (χ ≠ 1 ∨ ρ ≠ 1) → LFunction χ ρ = 0 → |ρ.im| ≤ 1 → c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ 1 - ρ.re := by
  first | exact @GlobalTheory.ZeroGapNearOne.exists_gap | exact GlobalTheory.ZeroGapNearOne.exists_gap | (intros; apply GlobalTheory.ZeroGapNearOne.exists_gap <;> assumption)
