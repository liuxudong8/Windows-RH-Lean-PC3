import BSD.EulerSystem
import BSD.Sha11_389
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open BSD.EulerSystem
open BSD.Sha11_389

namespace BSD.GrHChain389

/-!
# GRH 条件链（拆环版）：四环责任表 + 组合真证（2026-10-16）

背景：G5/G6（Probe389/G5_GRHBound/g5_result.md）把"GRH + 精细 BSD ⟹ #Ш(389a1) = 1"
的条件链数值闭合。本模块把原单 axiom `grh_sha_order_bound_389` **拆成四环**，
每环独立命名、独立标注性质（猜想 / 数值 / 定理），并用**实数组合真证**把它们
拼回 `ShaPOrder Curve389a1 11 ≤ 3`——责任边界画清，后续"摘 GRH"或"精细 BSD
降级为定理"只改对应一环。

## 四环责任表

| 环 | Lean 对象 | 内容 | 性质 | 升级路径 |
|---|---|---|---|---|
| 环 1 | （数学层记录） | GRH 偏和界：∃ C₁,k, ∀ x ∈ [x₀,10⁶], |S(x)| ≤ C₁√x(logx)^k（实测 sup：k=1: 11.171、k=2: 0.810、k=3: 0.135） | GRH 推论 + 经验常数 | 步 2：C₁ 证明型显式常数（Bach/Rosser 零点枚举，不需 GRH）⟹ GRH 退役 |
| 环 2 | `mellin_tail_bound_389` | |L″(1)/2| ≤ Mbound₃₈₉，Mbound = M(t₀)+E(t₀)，取最紧组合 (k=2, t₀=10⁷)：M+E = 0.857 | 解析推导真 + 数值求和（GRH 常数已吸收进 E(t₀)） | 环 1 证明化后 Mbound 数值自动带证书 |
| 环 3 | `fine_bsd_389` | #Ш·Ω·Reg = L″(1)/2（精细 BSD，389a1 秩 2） | 数学猜想（秩 2 无定理） | 步 3：CH22 generalized Kato 类 + Iwasawa 主猜想 ⟹ p-adic 侧；或保持 axiom |
| 环 4 | `omega_reg_min_bound_389`（**定理**） | Ω·Reg·∏c ≥ Ω·Reg_min = 0.759291598 | **真证**（Ω、Reg 两条区间锚点 + `mul_le_mul` + `norm_num`；2026-11-27 由 axiom 降级） | Reg 证明型下界（依赖高度配对基础设施） |

组合真证 `sha_bound_three_from_chain`：环 2 + 环 3 + 环 4 ⟹
  |#Ш·Ω·Reg| = |L″/2| ≤ Mbound ∧ Ω·Reg ≥ Ωmin > 0
  ⟹ #Ш ≤ Mbound/Ωmin = N₀ < 4 ⟹ #Ш ≤ 3（整数化）。

**Lean 状态说明**：
- 环 1（S(x) 偏和）未进入 Lean 对象层——`S(x)` 是自守 L 函数的偏和，mathlib 无定义
  （机械化缺口，属步 4）；其数值作用已被环 2 的 `Mbound389` 吸收。诚实起见以数学层
  docstring 完整记录，不伪造 Lean 断言。
- `Lpp389`/`Omega389`/`Reg389` 是解析/代数对象，以**不透明 axiom**声明（与
  `BSD.Positivity` 的 `OmegaE`/`RegulatorE` 同一口径）。2026-11-27 修正：原写法把
  `Lpp389`、`OmegaReg389` 定义成常数 `0`，与环 4 的下界 `0.759291598 ≤ Ω·Reg`
  直接矛盾（0.759291598 ≤ 0），整个模块成了"由矛盾推 #Ш ≤ 3"的空链——见下节。
- `Mbound389`/`OmegaRegMin389` 为真实数值（可 norm_num 精确验证的 ℝ 字面量）。

判定链数值（G5 修正版框架）：
  - 引理 1（环 1，GRH 偏和界）：|S(x)| = |Σ_{n≤x} a_n| ≤ C₁√x (log x)^k；
  - 引理 2（环 2，Mellin 积分）：L″(1)/2 = (1/2)∫₁^∞ S(x)x^{−2}((log x)² − 2log x)dx，
    离散化 M(t₀) = (1/2)Σ_{n=1}^{t₀−1} S(n)[(log n)²/n − (log(n+1))²/(n+1)]；
  - 定理（环 2）：|L″(1)/2| ≤ M(t₀) + E(t₀)，E(t₀) = C₁·2^{k+3}(k+2)!/(2√t₀)；
  - 推论（组合）：#Ш ≤ N₀(t₀, C₁) = [M(t₀)+E(t₀)]/(Ω·Reg_min·∏c)，∏c = 1（389 半稳定）。

M(t₀) 收敛（锚点 L″/2 = 0.759316500288）：
  | t₀ | M(t₀) |
  | 10³ | 0.80503 | 10⁴ | 0.79574 | 10⁵ | 0.78285 | 10⁶ | 0.75817 | 10⁷ | 0.76121 |
  （10⁶/10⁷ 在锚点两侧振荡收敛，量级 (log X)²/√X ✓）

N₀ 判定表（Ω·Reg_min = 0.759291598；阈值 4·Ω·Reg_min = 3.037166；全组合 N₀ < 4 ✓；
  本模块取最紧组合 (k=2, t₀=10⁷)：M+E = 0.857，N₀ = 1.128）：
  | (k, t₀) | E(t₀) | M+E | N₀ |
  | (1,10⁶) | 0.536 | 1.294 | 1.705 |
  | (1,10⁷) | 0.170 | 0.928 | 1.222 |
  | (2,10⁶) | 0.311 | 1.069 | 1.408 |
  | (2,10⁷) | 0.098 | 0.857 | **1.128** |
  | (3,10⁶) | 0.517 | 1.275 | 1.679 |
  | (3,10⁷) | 0.163 | 0.922 | 1.214 |

诚实边界（G5 §4）：
  - 环 1 的 C₁, k 为经验值（x ≤ 10⁶ 的 sup），非证明常数；判定稳健性（≥7× 余量）
    使其为工程而非数学障碍——C₁ 容许放大：k=2,t₀=10⁶ 7.3×、k=2,t₀=10⁷ 23×、
    k=1,t₀=10⁷ 13×、k=3,t₀=10⁷ 14×；
  - 环 3（精细 BSD）为 axiom：结论是"GRH + 精细 BSD ⟹ #Ш=1"；无 BSD 则仅给
    "若 BSD 数值成立则 #Ш=1"（G2a 已覆盖）；
  - Reg 用数值（G3 四源一致 ~10⁻¹⁹）——Reg_min 吸收误差；证明型下界未做；
  - GRH 不给 Ш 整体有限性（G1 保持开放）——本链只约束"若有限则阶"。

组合收口（本模块真证）：#Ш ≤ N₀ < 4 ⟹ #Ш ≤ 3 ∧ #Ш 是平方数（Cassels）∧ 1 ≤ #Ш
⟹ #Ш = 1 ⟹ Ш[11] = 1（11⁰ = 1）。

对象：#Ш[11] = ShaPOrder Curve389a1 11（Sha11_389 命名空间）。
-/

-- ============ 环 1：GRH 偏和界（数学层记录，Lean 未定义 S(x)） ============

/-! **环 1 · GRH 偏和界（数学层记录，不进 Lean 对象层）**：
    存在经验常数 (C₁, k)，使偏和 |S(x)| = |Σ_{n≤x} a_n| ≤ C₁√x·(log x)^k
    对 x ∈ [x₀, 10⁶] 成立（实测 sup：k=1: 11.171@x=973986、k=2: 0.810@x=973986、
    k=3: 0.135@x=105；源 g5_data.sage）。
    数学作用：环 2 尾部界 E(t₀) = C₁·2^{k+3}(k+2)!/(2√t₀) 的常数来源。
    **Lean 状态**：`S(x)`（自守 L 函数偏和）mathlib 未定义——本环不伪造 Lean 断言，
    以 docstring 完整记录；其数值作用经环 2 的 `Mbound389`（M+E = 0.857）吸收。
    升级路径（步 2）：Bach/Rosser 型显式零点枚举 + 显式公式余项给出证明型 C₁——
    显式公式零点项用平凡界 Re(ρ) ≤ 1 + 有限枚举 + 密度估计控制，**不需 GRH**，
    届时环 1 退役、GRH 从链上摘除。 -/
-- （无 Lean axiom；见上方 docstring。）

-- ============ 数值锚点（ℝ 对象声明 + 真实数值） ============

/-! ### 【2026-11-27 修正 · Reg 分母】原写法与环 4 自相矛盾

原：`noncomputable def Lpp389 : ℝ := 0`、`noncomputable def OmegaReg389 : ℝ := 0`，
配合 `axiom omega_reg_min_bound_389 : 0.759291598 ≤ OmegaReg389` 与
`axiom sha_order_at_least_one : 1 ≤ ShaPOrder`、`axiom fine_bsd_389 : #Ш·ΩReg = Lpp`，
可推出 `0.759291598 ≤ 0`（即 `False`）与 `#Ш·0 = 0`——所谓"组合真证 #Ш ≤ 3"
是从矛盾推出的空结论，G5 链在 Lean 侧实为**空壳**。

现修法：三个数值对象改为不透明 axiom（对象声明不等于数学假设，与 Positivity 层同口径）；
**Ω 与 Reg 拆开**，分母 `Ω·Reg·∏c` 由结构定义给出，其下界 `≥ 0.759291598`
改由两条双侧区间锚点 + `mul_le_mul` + `norm_num` **真证**（原环 4 的 axiom 降为定理）。 -/

/-- L″(E/ℚ,1)/2：解析对象（不透明；真实值 0.759316500288，四锚点之一）。 -/
axiom Lpp389 : ℝ

/-- Ω(E/ℚ)：实周期（不透明对象；G3 四源值 4.98042512171）。 -/
axiom Omega389 : ℝ

/-- Reg(E/ℚ)：秩 2 高度配对正则子 = det(高度配对矩阵)（不透明对象；
    G3 Sage regulator(precision=200) = 0.1524601779431437516243247570494558…）。 -/
axiom Reg389 : ℝ

/-- ∏c_p = 1（389 半稳定：c₃₈₉ = 1，其余无）。 -/
def prodC389 : ℝ := 1

/-- 分母 Ω·Reg·∏c：结构定义（不是断言）。 -/
noncomputable def OmegaReg389 : ℝ := Omega389 * Reg389 * prodC389

/-- M(t₀) + E(t₀)：Mellin 离散化和 + 尾部界，取最紧组合 (k=2, t₀=10⁷)，
    M = 0.76121、E = 0.098 ⟹ M+E = 0.857（g5_result.md N₀ 判定表）。 -/
noncomputable def Mbound389 : ℝ := 857 / 1000

/-- Ω·Reg_min：Ω·Reg 的数值下界锚点（G3 四源一致 ~10⁻¹⁹），
    阈值 4·Ω·Reg_min = 3.037166。 -/
noncomputable def OmegaRegMin389 : ℝ := 759291598 / 10^9

/-- **Ω 双侧区间锚点（G3）**：4.9804 ≤ Ω ≤ 4.9805（真值 4.98042512171 落在内，
    半宽 5×10⁻⁵ ≫ 四源差 ~10⁻¹¹）。 -/
axiom omega_bracket_389 : (4.9804 : ℝ) ≤ Omega389 ∧ Omega389 ≤ (4.9805 : ℝ)

/-- **Reg 双侧区间锚点（G3，200 位）**：0.1524600 ≤ Reg ≤ 0.1524602
    （真值 0.15246017794314375162432… 落在内；半宽 2×10⁻⁷ ≫ 四源差 ~10⁻¹⁹）。 -/
axiom reg_bracket_389 : (0.1524600 : ℝ) ≤ Reg389 ∧ Reg389 ≤ (0.1524602 : ℝ)

/-- 分母正性（真证：Ω ≥ 4.9804 > 0 ∧ Reg ≥ 0.15246 > 0）。 -/
theorem omega_reg_pos_389 : 0 < OmegaReg389 := by
  obtain ⟨hOlo, _⟩ := omega_bracket_389
  obtain ⟨hrlo, _⟩ := reg_bracket_389
  have hO : 0 < Omega389 := by linarith
  have hr : 0 < Reg389 := by linarith
  have hc : 0 < prodC389 := by norm_num [prodC389]
  unfold OmegaReg389
  exact mul_pos (mul_pos hO hr) hc

/-- **环 4（axiom → 真证）**：Ω·Reg·∏c ≥ 0.759291598。
    乘法下界：4.9804 × 0.1524600 = 0.759311784 ≥ 0.759291598（norm_num 精确有理）。 -/
theorem omega_reg_min_bound_389 : OmegaRegMin389 ≤ OmegaReg389 := by
  obtain ⟨hOlo, _⟩ := omega_bracket_389
  obtain ⟨hrlo, _⟩ := reg_bracket_389
  have hOpos : 0 ≤ Omega389 := by linarith
  have hprod : (4.9804 : ℝ) * 0.1524600 ≤ Omega389 * Reg389 :=
    mul_le_mul hOlo hrlo (by norm_num) hOpos
  have hbase : OmegaRegMin389 ≤ (4.9804 : ℝ) * 0.1524600 := by
    norm_num [OmegaRegMin389]
  rw [OmegaReg389, prodC389, mul_one]
  linarith [hbase, hprod]

/-- **锚点可满足性（真证）**：Ω、Reg 的两条区间锚点与分母下界在 ℝ 中**同时可实现**，
    witness (Ω, Reg) = (4.9804, 0.1524600)：4.9804·0.1524600 = 0.759311784 ≥ 0.759291598。
    这条定理的作用是**排空链**：2026-11-27 前的写法（`OmegaReg389 := 0` ∧ `0.759291598 ≤ Ω·Reg`）
    自身矛盾、可由它推出 `False`；现在同一组锚点有一个显式实数模型，故环 4 不再是空断言。 -/
theorem anchor_consistent_389 : ∃ O R : ℝ,
    (4.9804 : ℝ) ≤ O ∧ O ≤ 4.9805 ∧
    (0.1524600 : ℝ) ≤ R ∧ R ≤ 0.1524602 ∧
    (759291598 / 10^9 : ℝ) ≤ O * R := by
  refine ⟨4.9804, 0.1524600, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- ============ 环 2–4：独立挂账（逐环可独立升级） ============

/-- **环 2 · Mellin 尾部界**：|L″(1)/2| ≤ Mbound₃₈₉。
    依据：Mellin 积分修正表示（L″(1)/2 = (1/2)∫₁^∞ S(x)x^{−2}((logx)²−2logx)dx）
    + 离散化 M(t₀) + 尾部绝对收敛界 E(t₀)（环 1 常数进入）。
    解析推导为真，求和/尾数为数值；GRH 经验常数已吸收进 Mbound 数值。
    升级路径：环 1 的 C₁ 证明化（步 2）⟹ 本环数值自动带证书。 -/
axiom mellin_tail_bound_389 : |Lpp389| ≤ Mbound389

/-- **环 3 · 精细 BSD（389a1，秩 2）**：#Ш·Ω·Reg = L″(1)/2。
    数学猜想（秩 2 精细 BSD 无一般定理）；数值对账（L″/2 = 0.759316500288 vs
    Ω·Reg·#Ш，#Ш=1 时 G3/G4 四源一致 ~10⁻¹⁹）是证据非证明。
    升级路径（步 3）：CH22 generalized Kato 类（恰做 389a1 秩 2 类非零）+
    Iwasawa 主猜想 ⟹ p-adic 侧精细 BSD；全局对账仍需局部因子。 -/
axiom fine_bsd_389 : (ShaPOrder Curve389a1 11 : ℝ) * OmegaReg389 = Lpp389

/-! **环 4 · Ω·Reg 锚点下界（2026-11-27：axiom → theorem）**：Ω·Reg·∏c ≥ 0.759291598。
    推导链：`omega_bracket_389`（Ω ≥ 4.9804）∧ `reg_bracket_389`（Reg ≥ 0.1524600）
    ⟹ `mul_le_mul` ⟹ 4.9804×0.1524600 = 0.759311784 ≥ 0.759291598（`norm_num`）。
    原 axiom 的依据（Ω、Reg 的 G3 四源值）现在落在两条区间锚点上，环 4 本身不再断言数值。
    升级路径：Reg 的证明型下界（对象级高度配对，依赖 mathlib canonical height
    基础设施——与 RankTwo389 的 height_pairing_det_pos_389 同源）。 -/
-- （定理已在"数值锚点"节给出：`omega_reg_min_bound_389`。）

-- ============ 组合真证：环 2+3+4 ⟹ #Ш ≤ 3 ============

/-- **组合真证**：环 2 + 环 3 + 环 4 ⟹ #Ш(389a1) ≤ 3。
    实数链：|#Ш·Ω·Reg| = |L″/2| ≤ Mbound（环 3 等式 + 环 2 界 + 非负性）
    ⟹ #Ш·Ω·Reg ≤ Mbound ⟹ #Ш·Ωmin ≤ #Ш·Ω·Reg（环 4）⟹ #Ш ≤ Mbound/Ωmin = N₀
    （`le_div_iff₀`，Ωmin > 0）⟹ N₀ < 4（norm_num 精确有理）⟹ #Ш < 4
    （`exact_mod_cast`）⟹ #Ш ≤ 3（`Nat.lt_succ_iff`）。
    零猜想级输入：三个 axiom 均为数值/猜想挂账，组合逻辑本身是真证。 -/
theorem sha_bound_three_from_chain : ShaPOrder Curve389a1 11 ≤ 3 := by
  have hOm_pos : 0 < OmegaRegMin389 := by
    norm_num [OmegaRegMin389]
  have hReg_pos : 0 < OmegaReg389 := lt_of_lt_of_le hOm_pos omega_reg_min_bound_389
  have hprod_nonneg : 0 ≤ (ShaPOrder Curve389a1 11 : ℝ) * OmegaReg389 :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt hReg_pos)
  have hLpp_nonneg : 0 ≤ Lpp389 := by
    rw [← fine_bsd_389]
    exact hprod_nonneg
  have hLpp_abs : |Lpp389| = Lpp389 := abs_of_nonneg hLpp_nonneg
  have hmellin : |Lpp389| ≤ Mbound389 := mellin_tail_bound_389
  have hLpp_le : Lpp389 ≤ Mbound389 := by
    rw [hLpp_abs] at hmellin
    exact hmellin
  have hprod_le : (ShaPOrder Curve389a1 11 : ℝ) * OmegaReg389 ≤ Mbound389 := by
    rw [fine_bsd_389]
    exact hLpp_le
  have hmult : (ShaPOrder Curve389a1 11 : ℝ) * OmegaRegMin389 ≤
      (ShaPOrder Curve389a1 11 : ℝ) * OmegaReg389 :=
    mul_le_mul_of_nonneg_left omega_reg_min_bound_389 (Nat.cast_nonneg _)
  have hSha_le : (ShaPOrder Curve389a1 11 : ℝ) ≤ Mbound389 / OmegaRegMin389 := by
    exact (le_div_iff₀ hOm_pos).mpr (le_trans hmult hprod_le)
  have hN0_lt4 : Mbound389 / OmegaRegMin389 < (4 : ℝ) := by
    norm_num [Mbound389, OmegaRegMin389]
  have hSha_lt4 : (ShaPOrder Curve389a1 11 : ℝ) < (4 : ℝ) := lt_of_le_of_lt hSha_le hN0_lt4
  have hSha_lt4_nat : ShaPOrder Curve389a1 11 < 4 := by
    exact_mod_cast hSha_lt4
  exact Nat.lt_succ_iff.mp hSha_lt4_nat

-- ============ Cassels 平方性 + 非平凡下界（组合收口输入） ============

/-- **Cassels 配对平方性**：#Ш(389a1) 的阶是平方数（有限时；Cassels–Tate 配对
    非退化交错 ⟹ |Ш| = |Ш^| 且为平方）。对 #Ш=1 平凡满足（1=1²）；
    本 axiom 是组合真证排除 #Ш ∈ {2,3} 的关键输入。 -/
axiom sha_square_389 : ∃ m : ℕ, ShaPOrder Curve389a1 11 = m ^ 2

/-- **结构事实**：#Ш[p](E/ℚ) 的阶 ≥ 1（有限阿贝尔群恒含平凡元素；
    ShaPOrder 定义为群阶）。 -/
axiom sha_order_at_least_one (E : Type) (p : ℕ) : 1 ≤ ShaPOrder E p

-- ============ 组合收口真证 ============

/-- **组合真证**：#Ш(389a1) = 1，由拆环链（环 2+3+4 ⟹ #Ш ≤ 3）
    + Cassels 平方性 + 非平凡下界推出：
    #Ш ≤ 3 ∧ #Ш = m² ∧ 1 ≤ #Ш ⟹ m² ≤ 3 ∧ 1 ≤ m² ⟹ m = 1 ⟹ #Ш = 1。
    ——G5/G6 的"GRH 反证链"在 Lean 侧的真证部分（数值上界挂账，组合逻辑真证）。 -/
theorem sha11_one_of_grh_fine_bsd_389 : ShaPOrder Curve389a1 11 = 1 := by
  have h1 : 1 ≤ ShaPOrder Curve389a1 11 := sha_order_at_least_one Curve389a1 11
  have h2 : ShaPOrder Curve389a1 11 ≤ 3 := sha_bound_three_from_chain
  rcases sha_square_389 with ⟨m, hm⟩
  have hm_le : m ^ 2 ≤ 3 := by
    rw [hm] at h2
    exact h2
  have hm_ge : 1 ≤ m ^ 2 := by
    rw [hm] at h1
    exact h1
  have hm_lt2 : m < 2 := by
    by_contra hnot
    have hge : 2 ≤ m := Nat.ge_of_not_lt hnot
    have hsq : 4 ≤ m ^ 2 := by
      have hmul : 2 * 2 ≤ m * m := Nat.mul_le_mul hge hge
      calc
        4 = 2 * 2 := by norm_num
        _ ≤ m * m := hmul
        _ = m ^ 2 := by ring
    have h43 : (4 : ℕ) ≤ 3 := le_trans hsq hm_le
    norm_num at h43
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    rw [hm0] at hm_ge
    norm_num at hm_ge
  have hm_ge1 : 1 ≤ m := by
    have hpos : 0 < m := Nat.pos_iff_ne_zero.mpr hm_ne0
    simpa using (Nat.succ_le_of_lt hpos)
  have hm_le1 : m ≤ 1 := Nat.lt_succ_iff.mp hm_lt2
  have hm_eq : m = 1 := Nat.le_antisymm hm_le1 hm_ge1
  rw [hm, hm_eq]
  norm_num

end BSD.GrHChain389
