import A5CharQ5.A5Defs

open Representation

instance : Fintype G := Fintype.ofFinite G

/-- 枚举完整性：60 个元素。 -/
example : (Finset.univ : Finset G).card = 60 := by native_decide

/-- Equiv.Perm 的 DecidableEq 是否可执行。 -/
example : (decide ((sG : G) = sG)) = true := by native_decide

/-- 可执行共轭判定：∃ h, h * g = c * h。 -/
def conjB (g c : G) : Bool :=
  (Finset.univ : Finset G).any (fun h => decide (h * g = c * h))

/-- 类覆盖（Bool 形式）。 -/
example : (Finset.univ : Finset G).all (fun g =>
    decide (g = 1) || conjB g (sG ^ 2 * tG) || conjB g tG || conjB g sG
      || conjB g (sG ^ 2)) = true := by
  native_decide

/-- 类大小（Bool filter 计数）。 -/
example : ((Finset.univ : Finset G).filter (fun g => conjB g tG)).card = 20 := by
  native_decide
