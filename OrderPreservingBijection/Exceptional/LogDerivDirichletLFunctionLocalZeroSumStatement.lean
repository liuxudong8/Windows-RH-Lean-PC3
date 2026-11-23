import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic
import OrderPreservingBijection.Exceptional.LogDerivDirichletLFunctionLocalZeroSum
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDeriv_dirichletLFunction_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.LLocal.logDeriv_LFunction_local | exact GlobalTheory.LLocal.logDeriv_LFunction_local | (intros; apply GlobalTheory.LLocal.logDeriv_LFunction_local <;> assumption)
