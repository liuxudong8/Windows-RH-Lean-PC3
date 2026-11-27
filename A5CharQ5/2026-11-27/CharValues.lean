import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.CategoryTheory.Simple
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import OrderPreservingBijection.QuadraticFieldFive
import A5CharQ5.A5Defs
import A5CharQ5.ConjClasses

/-!
# A₅ 3 维二十面体表示：不可约性（击破清单 #4）

`exists_five_order_char_phi` 与 `char_values_in_Q5` 已在 `A5Defs.lean` 尾部**真证**
（char_one / char_sG / char_tG / char_sG_sq / char_sG_sq_tG 五条代表元值 +
五个黄金引理的 ℂ 侧版本），本文件只保留尚未闭合的 `icosahedral_simple`，
不再重复声明（旧版本的两条 theorem 与 A5Defs 尾部同名，已删除）。

## 现状与技术障碍

目标：`CategoryTheory.Simple icosahedralRep`。

唯一现成判据是 `FDRep.simple_iff_char_is_norm_one`：

    Simple V ↔ ∑ g, V.character g * V.character g⁻¹ = ↑(Nat.card G)

右端 = 60。按共轭类分组：

    类   代表元        大小   χ 值
    1    1              1     3
      2A  sG²·tG        15    -1
    3A    tG            20     0
    5A    sG            12    α = (1+√5)/2 = φ
    5B    sG²           12    1-α = φ̄

    9·1 + 1·15 + 0·20 + (α² + (1-α)²)·12
    = 24 + (φ + φ̄ + 2)·12 = 24 + 3·12 = 60 ✓

## 为什么不能穷举

`Fintype (alternatingGroup α)` 由 mathlib 定义为 `Subtype.fintype _ _ sign.decidableMemKer _`，
是 **noncomputable**（底层 `Fintype (Perm α)` 走有限性而非可执行枚举）。
实测 `native_decide` 报 `depends on 'Fintype.ofFinite', which is 'noncomputable'`，
`decide` 则因 `Fintype.ofFinite` 的 `univ` 不可核归约而同样不可用。
因此必须走**群论论证**（cycle type 分类 + A₅ 内共轭 + 类大小），而不是元素穷举。

## 可用的 mathlib 工具（已实测存在）

- `Equiv.Perm.isConj_iff_cycleType_eq`：同 cycle type ⟺ 共轭（Sₙ 内）
- `alternatingGroup.isConj_of`：Sₙ 内共轭 ⟹ Aₙ 内共轭，条件 `support.card + 2 ≤ n`
- `alternatingGroup.isThreeCycle_isConj`：Aₙ 中两个 3-循环必共轭（`5 ≤ Nat.card α`）
- `FDRep.char_conj`：`V.character (h * g * h⁻¹) = V.character g`（类函数性）
- `alternatingGroup.isSimpleGroup`（A₅ 单群）
-/

noncomputable section

open Representation

/-- A₅ 的二十面体表示不可约（击破清单 #4，已闭合）。

当初带 `sorry` 时降为 `theorem`，以免全局实例投喂未证前提；现已真证，可安全改回 `instance`。
路径：`simple_iff_char_is_norm_one` ← `icosahedral_char_sum`（五段求和 = 60）← 共轭类分类。 -/
theorem icosahedral_simple : CategoryTheory.Simple icosahedralRep := by
  rw [FDRep.simple_iff_char_is_norm_one]
  rw [card_G]
  exact icosahedral_char_sum
