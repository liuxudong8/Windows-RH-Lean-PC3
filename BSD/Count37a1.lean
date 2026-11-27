import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

/-!
# 37a1 的有限域点计数（BSD.Count37a1）

E : y² + y = x³ − x（Δ = −37，坏约化仅 𝔭 = 37），故 p = 2、3 均为好约化。

本模块只做一件可判定的事：在 `ZMod p` 上枚举仿射点，得

- #E(𝔽₂) = 5（仿射 4 + 无穷远点 O）
- #E(𝔽₃) = 7（仿射 6 + O）

两数互素。配合"好约化处挠群单射"这一条标准事实（在 `BSD.Main` 作定理级挂账，
参照 389a1 的 `N₅ = 9`、`N₇ = 13` 同型做法），即得 E(ℚ)[tors] = {O}。

与 389a1 的差别：那里的 N₅ = 9、N₇ = 13 是库外纯枚举"复算"（挂账为数值锚点）；
这里的 5 与 7 是**Lean 内 `native_decide` 真证**，只信任 2 次具体计算的执行。
-/

namespace BSD.Count37a1

/-- E = 37a1 在 𝔽_p 上的仿射点计数（不含无穷远点 O）。 -/
def nAff (p : ℕ) [NeZero p] : ℕ :=
  (Finset.univ.filter
    (fun q : ZMod p × ZMod p => q.2 ^ 2 + q.2 = q.1 ^ 3 - q.1)).card

/-- E = 37a1 在 𝔽_p 上的点计数（含 O）。 -/
def nPoints (p : ℕ) [NeZero p] : ℕ := nAff p + 1

/-- #E(𝔽₂) = 5（仿射 (0,0),(0,1),(1,0),(1,1) 四点 + O）。
    a₂ = 3 − 5 = −2，与 LSeries5 的 `ap_E` 表一致。 -/
theorem nPoints_two : nPoints 2 = 5 := by native_decide

/-- #E(𝔽₃) = 7（仿射 6 点 + O）。a₃ = 4 − 7 = −3。 -/
theorem nPoints_three : nPoints 3 = 7 := by native_decide

/-- gcd(#E(𝔽₂), #E(𝔽₃)) = gcd(5, 7) = 1。 -/
theorem coprime_counts : Nat.Coprime (nPoints 2) (nPoints 3) := by
  rw [nPoints_two, nPoints_three]
  decide

end BSD.Count37a1
