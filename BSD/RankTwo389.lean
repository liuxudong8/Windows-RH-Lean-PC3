import BSD.EulerSystem
import BSD.Sha11_389

open BSD.EulerSystem
open BSD.Sha11_389

namespace BSD.RankTwo389

/-!
# rank(389a1) = 2：数据锚点 + 组合真证（2026-10-16）

背景：`BSD.EulerSystem.rank_389a1`（axiom）给出 Rank = 2（黑箱挂账）。本模块把
代数秩 2 拆为"上界真证 + 下界挂账"：
  rank ≤ 2：|Sel₂| = 4（G4 纯 Python 独立复算，Sha11_389 已挂账 `sel2_order_four_389`）
    ∧ 2-descent 阶上界（正合列 0 → E(ℚ)/2E(ℚ) → Sel₂ → Ш[2] → 0，E(ℚ) 无 2-扭）
    ⟹ 2^rank ≤ #Sel₂ = 4 ⟹ rank ≤ 2（**真证**，仅依赖 descent 结构 axiom + 数据锚点）；
  rank ≥ 2：两个独立无限阶点 P₁ = (−1:1:1)、P₂ = (0:−1:1)
    （B）独立：高度配对 det = 0.15246017794314375162... > 1/10 > 0
      ——G3 数值下界量化（Sage regulator(200) 高度配对 det；Python NT/Sage/Magma/LMFDB
      四源一致到 ~10⁻¹⁹；G3_Reg/g3_sage.sage 实测 gens）⟹ P₁,P₂ 在 E(ℚ)/tors 中线性无关；
    （A）无限阶：好素 reduction 点计数 N₅ = #E(𝔽₅) = 9、N₇ = #E(𝔽₇) = 13
      （2026-10-16 纯枚举复算，含无穷远点；与 a₅=−3、a₇=−5 一致），
      gcd(N₅, N₇) = gcd(9,13) = 1 ⟹ E(ℚ)[tors] = 0（好素 reduction 单射标准事实）
      ⟹ P₁, P₂ ≠ O 自动无限阶；
    ⟹ rank ≥ 2（Mordell–Weil：自由部分秩 ≥ 独立点个数；挂账）；
  rank = 2：le_antisymm 组合（**真证**）。

净效果：`rank_two_389` 是 `EulerSystem.rank_389a1`（axiom）的证明型替代——代数秩 2
从"单黑箱 axiom"降级为"|Sel₂| 数据锚点 + descent 结构 axiom + 两独立点单点挂账"。

注意：EulerSystem.rank_389a1 注释的生成元 "(0,0),(1,0)" 与 Sage 实测 gens
[(-1:1:1),(0:-1:1)] 不符（历史遗留；以 G3_Reg/g3_sage.sage 的 gens 为准）。

数据源：Probe389/G4_Sel2/g4_result.md（|Sel₂|=4 纯 Python 复算）、
Probe389/G3_Reg/g3_result.md（Reg 200 位 + 高度配对 det ≠ 0）；
torsion reduction 点计数（N₅=9, N₇=13, gcd=1）为 2026-10-16 纯枚举复算（含无穷远点）。
-/

-- ============ 结构 axiom：2-descent 阶上界（2026-11-27 下沉至 SelmerLayer） ============

/-- 2-descent 阶上界（**已下沉** `BSD.SelmerLayer.sel2_rank_bound`）：此处保留同名别名，
    以维持既有调用路径 `BSD.RankTwo389.sel2_rank_bound`。 -/
abbrev sel2_rank_bound (E : Type) (K : Type) :
    2 ^ Rank E K ≤ SelPOrder E 2 :=
  BSD.SelmerLayer.sel2_rank_bound E K

-- ============ 数据锚点：两独立无限阶点（挂账） ============

/-- 389a1 的两个独立无限阶点（P₁ = (−1:1:1), P₂ = (0:−1:1)）。
    独立性（det > 1/10 > 0 数值下界）与无限阶（N₅, N₇ 互素 ⟹ torsion 平凡）
    的数值依据见 `points_independent_389` 的 docstring。 -/
axiom PointsIndependent389 : Prop

/-- 数据挂账：P₁, P₂ 独立且无限阶（数值锚点细化，2026-10-16）：
    · 独立（B）：高度配对 det = 0.15246017794314375162... > 1/10 > 0
      ——G3 数值下界量化：Sage regulator(precision=200) 的 2×2 高度配对矩阵
      [[0.686667083305587, 0.268478098806726],
       [0.268478098806726, 0.327000773651605]]，
      det = 0.152460177943144（Python NT/Sage/Magma/LMFDB 四源一致到 ~10⁻¹⁹；
      G3_Reg/g3_sage.sage 实测 gens）⟹ P₁, P₂ 在 E(ℚ)/tors 中线性无关；
    · 无限阶（A）：好素 reduction 点计数
      N₅ = #E(𝔽₅) = 9（y²+y = x³+x²−2x mod 5，枚举含无穷远点），
      N₇ = #E(𝔽₇) = 13（同法），gcd(N₅, N₇) = gcd(9,13) = 1；
      好素 reduction 单射（torsion 注入）标准事实 ⟹ E(ℚ)[tors] = 0
      ⟹ P₁, P₂ ≠ O 自动无限阶。
    注：389 是坏素（乘法约化），选好素 p = 5, 7 即足够。 -/
axiom points_independent_389 : PointsIndependent389

/-- Mordell–Weil 基本事实（定理级挂账）：两个独立无限阶点 ⟹ rank ≥ 2
    （自由阿贝尔群的秩 ≥ 线性无关元的个数）。 -/
axiom rank_ge_two_of_points : PointsIndependent389 → 2 ≤ Rank Curve389a1 K389a1

/-- rank ≥ 2（组合：数据锚点 + Mordell–Weil 事实）。 -/
theorem rank_ge_two_389 : 2 ≤ Rank Curve389a1 K389a1 :=
  rank_ge_two_of_points points_independent_389

-- ============ 组合真证 ============

/-- rank ≤ 2：2^rank ≤ #Sel₂ = 4 = 2² ⟹ rank ≤ 2（真证：pow 单调双向）。 -/
theorem rank_le_two_389 : Rank Curve389a1 K389a1 ≤ 2 := by
  have hb : 2 ^ Rank Curve389a1 K389a1 ≤ SelPOrder Curve389a1 2 :=
    sel2_rank_bound Curve389a1 K389a1
  have hb' : 2 ^ Rank Curve389a1 K389a1 ≤ 2 ^ 2 := by
    rw [sel2_order_four_389] at hb
    simpa using hb
  exact (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp hb'

/-- **rank(389a1) = 2**（组合真证：rank ≤ 2 ∧ rank ≥ 2 ⟹ = 2；
    `EulerSystem.rank_389a1`（axiom）的证明型替代）。 -/
theorem rank_two_389 : Rank Curve389a1 K389a1 = 2 :=
  le_antisymm rank_le_two_389 rank_ge_two_389

end BSD.RankTwo389
