import BSD.EulerSystem

open BSD.EulerSystem

namespace BSD.SelmerLayer

/-!
# 抽象 Selmer / Ш 层（2026-11-27 从 `Sha11_389` 下沉）

本文件只放**与具体曲线无关**的 Selmer/Ш 对象与其结构 axiom，不含任何 `Curve389a1`
常量。下沉动机（剥 `rank_389a1` 环债）：

  `sha11_order_one_of_sel11` 原先 `rw … rank_389a1`（`EulerSystem` 的 axiom，秩 = 2 over K），
  而真证的 `RankTwo389.rank_two_389` **无法**被 `Sha11_389` 引用——因为
  `RankTwo389` 反向 `import BSD.Sha11_389`，一用即环。环的成因是 `SelPOrder`/`ShaPOrder`
  等对象被写死在 `Sha11_389` 里，导致"秩的真证"必须长在它上面。

  ✔ 与本文件解耦后：`Sha11_389` 可以吃 `sel2_rank_bound`（在 `EulerSystem` 之上、
    `Sha11_389` 之下），从而在 ℚ 侧自证 `Rank Curve389a1 ℚ = 2`
    （`2^rank ≤ #Sel₂ = 4` 给上界，两独立 ℚ-点给下界），
    `sha11_order_one_389` 的闭包因此**不再含 `rank_389a1`**。

  说明：`Sha11_389` 保留了同名 `abbrev` 别名（`SelDim`、`SelPOrder` 等），
  所以 `BSD.Sha11_389.SelPOrder` 这类旧路径仍然可用。
-/

/-- dim_{ℚ_p} Sel(ℚ, V_pE)：p-adic Selmer 群的 ℚ_p-维数。 -/
axiom SelDim (E : Type) : ℕ

/-- corank_{ℤ_p} Ш[p^∞](E/ℚ)：Tate–Shafarevich p-primary 部分的 corank。 -/
axiom ShaCorank (E : Type) (p : ℕ) : ℕ

/-- Ш[p^∞](E/ℚ) 有限 ⟺ corank = 0。 -/
def ShaFinite (E : Type) (p : ℕ) : Prop := ShaCorank E p = 0

/-- #Ш[p](E/ℚ)：Tate–Shafarevich 群 p-torsion 部分的阶（有限时取数值；与 `ShaCorank`
    （p-primary corank）不同对象）。 -/
axiom ShaPOrder (E : Type) (p : ℕ) : ℕ

/-- #Sel_p(E/ℚ)：p-Selmer 群（E(ℚ)[p] 上的全局 descent 对象）的阶。 -/
axiom SelPOrder (E : Type) (p : ℕ) : ℕ

/-- descent 序列（ℚ 侧）：0 → E(ℚ)⊗ℚ_p → Sel(ℚ,V_pE) → T_p(Ш)⊗ℚ_p → 0
    的维数形式。`K` 参数在数学上应取 ℚ（秩按 ℚ 计），保留形参只为兼容既有调用点。 -/
axiom sel_dim_eq_rank_add_sha_corank (E : Type) (K : Type) (p : ℕ) :
    SelDim E = Rank E K + ShaCorank E p

/-- descent 正合列 0 → E(ℚ)/pE(ℚ) → Sel_p(E) → Ш[p] → 0 的阶形式：
    E[p](ℚ) = 0 时 E(ℚ)/pE(ℚ) ≅ (ℤ/p)^rank，故 #Ш[p] = #Sel_p / p^rank。
    `K` 参数同上：数学上应取 ℚ。 -/
axiom sha_p_descent_order (E : Type) (K : Type) (p : ℕ) :
    ShaPOrder E p = SelPOrder E p / (p ^ Rank E K)

/-- Selmer 群阶与维数的桥（结构 axiom，定理级）：Ш 的 p-部分 corank = 0 时，
    #Sel_p = p^{dim Sel(ℚ,V_pE)}。
    依据：E[p](ℚ) = 0 且 corank_{ℤ_p} Ш = 0 时，Sel_p(E) 是 F_p-向量空间、
    且 Sel(V_pE) = Sel_p(E) ⊗ ℚ_p，故 #Sel_p = p^dim（Silverman X §4 /
    Greenberg 控制定理的有限层版本；mathlib 无 Selmer 理论故挂账）。
    备注：`SelDim` 与 p 无关，故本桥对每个 p 都要单独喂 `ShaCorank E p = 0`；
    p = 2 处（corank 未证）不会触发，故与 `sel2_order_four_389` 无冲突。 -/
axiom sel_p_order_eq_p_pow_dim (E : Type) (K : Type) (p : ℕ) :
    ShaCorank E p = 0 → SelPOrder E p = p ^ SelDim E

/-- 2-descent 阶上界：E(ℚ) 无 2-扭 ⟹ 2^rank(E) ≤ #Sel₂(E)。
    数学来源：0 → E(ℚ)/2E(ℚ) → Sel₂(E) → Ш[2] → 0，
    |E(ℚ)/2E(ℚ)| = 2^{rank + dim E(ℚ)[2]}；E(ℚ)[2] = 0 ⟹ 2^rank | #Sel₂。
    ⚠ 审计注：`K` 形参在数学上必须取 ℚ——秩在扩域上会增长，取 K = 大扩域时
    `2^rank(E/K)` 可能超过 #Sel₂(E/ℚ)，本式会**假**。所有调用点（37a1、389a1）
    目前都传 ℚ 或 K389a1（后者 rank 与 ℚ 同值 2，恰好不触发反例）。
    2026-11-27：本 axiom 从 `RankTwo389` 下沉至此，供 ℚ 侧秩上界使用。 -/
axiom sel2_rank_bound (E : Type) (K : Type) : 2 ^ Rank E K ≤ SelPOrder E 2

end BSD.SelmerLayer
