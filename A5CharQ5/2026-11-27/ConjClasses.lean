/-
Copyright: A5CharQ5 项目
层 2 · #4 不可约性的共轭类结构层。

本文件的目标是为 `icosahedral_simple` 铺路：证 `∑ g, χ(g)χ(g⁻¹) = 60`，
需要「A₅ 的 5 个共轭类覆盖全部 60 元」与「类大小 1/15/20/12/12」两条组合事实。

### 已完成（第 1 步 · cycle type 分类）

`G_cycleType_cases`：A₅ 中每个元素的 cycle type 只能是 ∅、{3}、{5}、{2,2}。
对应 A₅ 的四个共轭类 1、3A、5A/5B、2A。

证明只用三条 mathlib 事实：
* `Equiv.Perm.sum_cycleType_le`：`cycleType.sum ≤ |α| = 5`
* `Equiv.Perm.two_le_of_mem_cycleType`：cycle type 的每项 ≥ 2
* `Equiv.Perm.sign_of_cycleType`：`sign f = (-1)^(sum + card)`，A₅ 中 sign = 1 ⟹ `sum + card` 偶

配合 `2 * card ≤ sum`（每项 ≥ 2）得 `card ≤ 2`，于是只剩下三个基数情形；
基数 1 时 `a ≥ 2`、`a ≤ 5`、`a + 1` 偶 ⟹ `a ∈ {3,5}`；
基数 2 时 `x + y ≥ 4`、`x + y ≤ 5`、`x + y + 2` 偶 ⟹ `x = y = 2`。

### 待完成（第 2–4 步）

2. 类覆盖：四种 cycle type 各自共轭到 `1 / sG²·tG / tG / sG 或 sG²`；
   5-循环的 A₅ 双分裂需单独处理（`sG` 与 `sG²` 在 A₅ 中不共轭）。
3. 类大小：轨道-稳定化子。
4. 分组求和收 60。

### 已排死的路线（勿重试）

`Fintype (alternatingGroup α)` 由 `Subtype.fintype _ _ sign.decidableMemKer _` 给出，
是 **noncomputable**；`native_decide` / `decide` 全部不可用，60 元素穷举无路。
-/
import A5CharQ5.A5Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.ConjAct

attribute [local instance] Classical.propDecidable

/-- multiset 每项 ≥ 2 时，`2 * card ≤ sum`。 -/
lemma two_mul_card_le_sum (t : Multiset ℕ) (h : ∀ a ∈ t, 2 ≤ a) : 2 * t.card ≤ t.sum := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 2 ≤ a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ b ∈ s, 2 ≤ b := fun b hb => h b (Multiset.mem_cons_of_mem hb)
    have := ih hs
    rw [Multiset.card_cons, Multiset.sum_cons]
    omega

/-- A₅ 中元素的 cycleType 基数 ≤ 2。 -/
lemma G_cycleType_card_le_two (g : G) : g.val.cycleType.card ≤ 2 := by
  have h2 : ∀ a ∈ g.val.cycleType, 2 ≤ a :=
    fun a ha => Equiv.Perm.two_le_of_mem_cycleType ha
  have h := two_mul_card_le_sum g.val.cycleType h2
  have h5 : g.val.cycleType.sum ≤ 5 := by
    have := Equiv.Perm.sum_cycleType_le g.val
    simpa using this
  omega

/-- A₅ 中元素满足 `Even (sum + card)`（符号为 +1 的等价形式）。 -/
lemma G_even_sum_add_card (g : G) : Even (g.val.cycleType.sum + g.val.cycleType.card) := by
  have hsign : g.val.sign = 1 := (MonoidHom.mem_ker).mp g.property
  have hn : (-1 : ℤˣ) ^ (g.val.cycleType.sum + g.val.cycleType.card) = 1 := by
    rw [← Equiv.Perm.sign_of_cycleType]
    exact hsign
  have hz : ((-1 : ℤ) ^ (g.val.cycleType.sum + g.val.cycleType.card) = 1) := by
    have hv := congrArg (fun u : ℤˣ => (u : ℤ)) hn
    simpa using hv
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hz

/-- **第 1 步**：A₅ 元素的 cycleType 只有四种 —— ∅、{3}、{5}、{2,2}。
    对应 A₅ 的四个共轭类 1、3A、5A/5B、2A。 -/
theorem G_cycleType_cases (g : G) :
    g.val.cycleType = 0 ∨ g.val.cycleType = {3} ∨
    g.val.cycleType = {5} ∨ g.val.cycleType = {2, 2} := by
  have hc : g.val.cycleType.card ≤ 2 := G_cycleType_card_le_two g
  have he : Even (g.val.cycleType.sum + g.val.cycleType.card) := G_even_sum_add_card g
  have h5 : g.val.cycleType.sum ≤ 5 := by
    have := Equiv.Perm.sum_cycleType_le g.val
    simpa using this
  have h2 : ∀ a ∈ g.val.cycleType, 2 ≤ a :=
    fun a ha => Equiv.Perm.two_le_of_mem_cycleType ha
  have hc3 : g.val.cycleType.card = 0 ∨ g.val.cycleType.card = 1 ∨
      g.val.cycleType.card = 2 := by omega
  rcases hc3 with h0 | h1 | h2c
  · left
    exact Multiset.card_eq_zero.mp h0
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h1
    have hmem : a ∈ g.val.cycleType := by rw [ha]; exact Multiset.mem_singleton.mpr rfl
    have ha2 : 2 ≤ a := h2 a hmem
    have hasum : a ≤ g.val.cycleType.sum := by rw [ha]; simp
    have ha5 : a ≤ 5 := le_trans hasum h5
    have hea : Even (a + 1) := by
      have h := he
      rw [ha, Multiset.sum_singleton, Multiset.card_singleton] at h
      simpa using h
    obtain ⟨k, hk⟩ := hea
    have : a = 3 ∨ a = 5 := by omega
    rcases this with rfl | rfl
    · right; left; exact ha
    · right; right; left; exact ha
  · obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp h2c
    have hmemx : x ∈ g.val.cycleType := by rw [hxy]; simp
    have hmemy : y ∈ g.val.cycleType := by rw [hxy]; simp
    have hx2 : 2 ≤ x := h2 x hmemx
    have hy2 : 2 ≤ y := h2 y hmemy
    have hsum : x + y ≤ 5 := by
      rw [hxy] at h5
      simpa using h5
    have hex : Even (x + y + 2) := by
      have h := he
      rw [hxy] at h
      simpa using h
    obtain ⟨k, hk⟩ := hex
    have hxy2 : x = 2 ∧ y = 2 := by omega
    right; right; right
    rw [hxy, hxy2.1, hxy2.2]

/- ------------------------------------------------------------------------ -/
-- 第 2 步（核心难点）：5-循环在 A₅ 中双分裂。
-- 不用 24 个 5-循环的组合计数，直接走特征标：
-- 若 sG 与 sG² 共轭，则 χ(sG²) = χ(sG)，即 α = 1-α ⟹ α = 1/2，
-- 而 α = (1+√5)/2 ≠ 1/2。故 5A ≠ 5B。
/- ------------------------------------------------------------------------ -/

/-- α = (1+√5)/2 ≠ 1/2。 -/
lemma alpha_ne_half : alpha ≠ (1 / 2 : ℂ) := by
  intro h
  have hr : ((1 + Real.sqrt 5) / 2 : ℝ) = 1 / 2 := by
    have hre := congrArg Complex.re h
    simpa [alpha] using hre
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- **5-循环双分裂**：`sG` 与 `sG²` 在 A₅ 中不共轭。
    即 A₅ 的两个 5-类 5A、5B 确实互不相同 —— 这是 χ 值 α 与 1-α 分别落在两类上的根源。 -/
theorem sG_not_isConj_sG_sq : ¬ IsConj (sG : G) (sG ^ 2) := by
  rintro ⟨c, hc⟩
  have hrel : (↑c : G) * sG * (↑c : G)⁻¹ = sG ^ 2 := by
    have hc' : (↑c : G) * sG = sG ^ 2 * (↑c : G) := hc
    rw [hc']
    group
  have hχ := FDRep.char_conj icosahedralRep sG (↑c : G)
  rw [hrel, char_sG_sq, char_sG] at hχ
  have h2 : 2 * alpha = 1 := by linear_combination hχ
  have ha : alpha = (1 / 2 : ℂ) := by
    rw [show (1 : ℂ) = 2 * (1 / 2 : ℂ) by norm_num] at h2
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2
  exact alpha_ne_half ha

/- ------------------------------------------------------------------------ -/
-- 第 2 步（续）：三类共轭的完整落地。
-- ∅ 类：元素是 1；{3} 类：3-循环全共轭；{2,2} 类：双换位全共轭（奇置换修正）。
/- ------------------------------------------------------------------------ -/

/-- cycleType 为空 ⟹ 元素是 1，故与 1 共轭。 -/
theorem G_cycleType_empty_isConj (g : G) (h : g.val.cycleType = 0) : IsConj g 1 := by
  have hv : g.val = 1 := Equiv.Perm.cycleType_eq_zero.mp h
  have hg : g = 1 := Subtype.ext hv
  subst hg
  exact ⟨1, by simp [SemiconjBy]⟩

/-- 所有 3-循环在 A₅ 中共轭（`IsThreeCycle` 的定义就是 cycleType = {3}）。 -/
theorem G_threeCycle_isConj (g : G) (h : g.val.cycleType = {3}) : IsConj g tG := by
  have hrep : (tG : Equiv.Perm (Fin 5)).cycleType = {3} := by decide
  exact alternatingGroup.isThreeCycle_isConj (α := Fin 5) (by simp) h hrep

/-- 对合 σ 与 `swap a (σ a)` 交换（(a, σa) 是 σ 的一个 2-循环）。 -/
theorem swap_commute_involution (σ : Equiv.Perm (Fin 5)) (hσ : σ ^ 2 = 1) (a : Fin 5)
    (ha : σ a ≠ a) :
    Equiv.swap a (σ a) * σ = σ * Equiv.swap a (σ a) := by
  have hsq : ∀ x, σ (σ x) = x := by
    intro x
    have h := congrArg (fun f : Equiv.Perm (Fin 5) => f x) hσ
    simpa [pow_two, Equiv.Perm.mul_apply] using h
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases h1 : x = a
  · rw [h1]
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left, hsq a]
  · by_cases h2 : x = σ a
    · rw [h2]
      rw [hsq a, Equiv.swap_apply_left, Equiv.swap_apply_right]
    · have h3 : σ x ≠ a := by
        intro hh
        apply h2
        rw [← hsq x, hh]
      have h4 : σ x ≠ σ a := by
        intro hh
        exact h1 (σ.injective hh)
      rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]

set_option maxHeartbeats 500000 in
/-- **{2,2} 类共轭**：所有双换位在 A₅ 中共轭于 `sG²·tG`。
    走 S₅ 共轭 + 奇置换修正：若 π 是奇置换，乘上 support 内的 `swap a (σ a)`
    （它与 σ 交换）即可把 π 变偶，而共轭关系不变。
    `alternatingGroup.isConj_of` 的充分条件要求 support.card + 2 ≤ 5，
    双换位 support = 4 只有一个不动点，故必须自建这条路线。 -/
theorem G_twoTwo_isConj (g : G) (h : g.val.cycleType = {2, 2}) :
    IsConj g (sG ^ 2 * tG : G) := by
  have h2 : (g.val : Equiv.Perm (Fin 5)) ^ 2 = 1 := by
    have hord : orderOf (g.val : Equiv.Perm (Fin 5)) = 2 := by
      rw [← Equiv.Perm.lcm_cycleType, h]
      simp
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hne : (g.val : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro hg
    have hz : (g.val : Equiv.Perm (Fin 5)).cycleType = 0 := by
      rw [hg]; exact Equiv.Perm.cycleType_one
    rw [hz] at h
    simp at h
  have hrep : ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)).cycleType = {2, 2} := by native_decide
  have hc : IsConj (g.val : Equiv.Perm (Fin 5)) ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)) := by
    apply Equiv.Perm.isConj_of_cycleType_eq
    rw [h, hrep]
  obtain ⟨πu, hπ⟩ := hc
  have hπ' : (↑πu : Equiv.Perm (Fin 5)) * (↑g : Equiv.Perm (Fin 5))
      = ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)) * (↑πu : Equiv.Perm (Fin 5)) := hπ
  rcases Int.units_eq_one_or (Equiv.Perm.sign (↑πu : Equiv.Perm (Fin 5))) with hs | hs
  · have hmem : (↑πu : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hs
    refine isConj_iff.2 ⟨⟨↑πu, hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : (↑πu : Equiv.Perm (Fin 5)) * (↑g : Equiv.Perm (Fin 5))
        * (↑πu : Equiv.Perm (Fin 5))⁻¹ = ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)) := by
      rw [hπ']
      rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [key]
    simp only [Subgroup.coe_mul]
  · obtain ⟨a, ha⟩ : ∃ a : Fin 5, (g.val : Equiv.Perm (Fin 5)) a ≠ a := by
      by_contra hall
      push_neg at hall
      exact hne (Equiv.ext hall)
    have hsne : a ≠ (g.val : Equiv.Perm (Fin 5)) a := fun hh => ha hh.symm
    have hcomm : Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a) * (g.val : Equiv.Perm (Fin 5))
        = (g.val : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a) :=
      swap_commute_involution g.val h2 a ha
    have hsign : Equiv.Perm.sign ((↑πu : Equiv.Perm (Fin 5))
        * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a)) = 1 := by
      rw [Equiv.Perm.sign_mul, hs, Equiv.Perm.sign_swap hsne, Int.units_mul_self]
    have hmem : ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))
        ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hsign
    refine isConj_iff.2 ⟨⟨(↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a),
      hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hcomm' : Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a) * (g.val : Equiv.Perm (Fin 5))
        * (Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))⁻¹ = (g.val : Equiv.Perm (Fin 5)) := by
      rw [hcomm]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have key : ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a)) * g.val
        * ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))⁻¹
        = ((sG ^ 2 * tG : G) : Equiv.Perm (Fin 5)) := by
      have e1 : ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a)) * g.val
          * ((↑πu : Equiv.Perm (Fin 5)) * Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))⁻¹
          = (↑πu : Equiv.Perm (Fin 5))
            * (Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a) * g.val
              * (Equiv.swap a ((g.val : Equiv.Perm (Fin 5)) a))⁻¹)
            * (↑πu : Equiv.Perm (Fin 5))⁻¹ := by
        rw [mul_inv_rev]
        simp only [mul_assoc]
      rw [e1]
      rw [hcomm']
      rw [hπ']
      rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [key]
    simp only [Subgroup.coe_mul]

/-- **第 2 步汇总**：四类 cycle type 各自的共轭类代表。
    {5} 类不进这条（其双分裂已由 `sG_not_isConj_sG_sq` 固定，两个 5-类需另论）。 -/
theorem G_cycleType_cases_isConj (g : G) (h : g.val.cycleType ≠ {5}) :
    (g.val.cycleType = 0 ∧ IsConj g 1)
      ∨ (g.val.cycleType = {3} ∧ IsConj g tG)
      ∨ (g.val.cycleType = {2, 2} ∧ IsConj g (sG ^ 2 * tG : G)) := by
  rcases G_cycleType_cases g with h0 | h3 | h5 | h22
  · left; exact ⟨h0, G_cycleType_empty_isConj g h0⟩
  · right; left; exact ⟨h3, G_threeCycle_isConj g h3⟩
  · exact absurd h5 h
  · right; right; exact ⟨h22, G_twoTwo_isConj g h22⟩
/-- **第 3 步（中心化子论证）**：A₅ 中 `sG` 的中心化子恰是 `<sG>` 本身。

    上界 `⟨sG⟩ ≤ C(sG)` 是平凡的（幂与自身交换）；下界靠基数相等：
    `Nat.card (C_{A₅}(sG)) ≤ Nat.card (C_{S₅}(sG)) = 5`，后者由 mathlib 的
    `Equiv.Perm.nat_card_centralizer` 对 `cycleType = {5}` 代入得
    `(5-5)! * 5 * 1! = 5`。桥接用 `Subtype.val` 构造注入 `C_{A₅} → C_{S₅}`。 -/
theorem G_centralizer_sG_eq_closure :
    Subgroup.centralizer ({sG} : Set ↑G) = Subgroup.closure ({sG} : Set ↑G) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · -- ⟨sG⟩ ≤ C(sG)
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    change ∀ h ∈ ({sG} : Set ↑G), h * sG = sG * h
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  · -- |C| ≤ |⟨sG⟩| = 5
    have hcl : Nat.card (Subgroup.closure ({sG} : Set ↑G)) = 5 := by
      rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, orderOf_sG]
    rw [hcl]
    have hinj : Function.Injective
        (fun x : Subgroup.centralizer ({sG} : Set ↑G) =>
          (⟨(x : ↑G).val, by
            change ∀ h ∈ ({sG.val} : Set (Equiv.Perm (Fin 5))),
              h * (x : ↑G).val = (x : ↑G).val * h
            intro h hh
            rw [Set.mem_singleton_iff] at hh
            rw [hh]
            exact congrArg Subtype.val (x.2 sG (Set.mem_singleton sG))⟩ :
            Subgroup.centralizer ({sG.val} : Set (Equiv.Perm (Fin 5))))) := by
      intro a b hab
      have hv : (a : ↑G).val = (b : ↑G).val :=
        congrArg (fun y : Subgroup.centralizer ({sG.val} : Set (Equiv.Perm (Fin 5))) =>
          (y : Equiv.Perm (Fin 5))) hab
      apply Subtype.ext
      apply Subtype.ext
      exact hv
    calc Nat.card (Subgroup.centralizer ({sG} : Set ↑G))
        ≤ Nat.card (Subgroup.centralizer ({sG.val} : Set (Equiv.Perm (Fin 5)))) :=
          Nat.card_le_card_of_injective _ hinj
      _ = 5 := by
          rw [Equiv.Perm.nat_card_centralizer]
          have hc : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
          rw [hc]
          norm_num

/-- **第 3 步**：`|C_{A₅}(sG)| = 5`。 -/
theorem G_centralizer_sG_card :
    Nat.card (Subgroup.centralizer ({sG} : Set ↑G)) = 5 := by
  rw [G_centralizer_sG_eq_closure]
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, orderOf_sG]

/-- **第 3 步**：A₅ 中 `sG` 的共轭类大小 = `|G| / |C(sG)| = 60 / 5 = 12`。

    用 `ConjClasses.card_carrier`（轨道-稳定化子）与
    `Subgroup.nat_card_centralizer_nat_card_stabilizer` 把中心化子接到
    `ConjAct` 稳定化子上。 -/
theorem G_class_sG_card : Nat.card (ConjClasses.mk sG).carrier = 12 := by
  haveI : Fintype ↑G := Fintype.ofFinite _
  haveI : Fintype (ConjClasses.mk sG).carrier := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (ConjAct ↑G) sG) := Fintype.ofFinite _
  have hS : Fintype.card (MulAction.stabilizer (ConjAct ↑G) sG) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    exact G_centralizer_sG_card
  have hG : Fintype.card ↑G = 60 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_G
  have hcard : Fintype.card (ConjClasses.mk sG).carrier = 12 := by
    rw [ConjClasses.card_carrier]
    rw [hG]
    rw [hS]
  rw [Nat.card_eq_fintype_card]
  exact hcard
/-- **第 3 步预备**：任意 `{5}`-型元素的阶 = 5（`lcm_cycleType` + `Subgroup.orderOf_coe`）。 -/
theorem G_fiveCycle_orderOf (g : G) (hg : g.val.cycleType = {5}) : orderOf g = 5 := by
  have h1 : orderOf (g.val : Equiv.Perm (Fin 5)) = 5 := by
    rw [← Equiv.Perm.lcm_cycleType, hg]
    simp
  rw [← Subgroup.orderOf_coe]
  exact h1

/-- **第 3 步预备**：S₅ 层 5-循环总数 = 24 = `4!`（`card_isConj_eq` 代入 `{5}`）。 -/
theorem perm_fiveCycle_count :
    Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {5}} = 24 := by
  have h24 : Nat.card {h : Equiv.Perm (Fin 5) | IsConj (sG.val : Equiv.Perm (Fin 5)) h} = 24 := by
    rw [Equiv.Perm.card_isConj_eq]
    have hc : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
    rw [hc]
    norm_num
  have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {5}}
      = {h : Equiv.Perm (Fin 5) | IsConj (sG.val : Equiv.Perm (Fin 5)) h} := by
    ext h
    have hc : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
    simp only [Set.mem_ofPred_eq]
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hc, eq_comm]
  rw [hset]
  exact h24

/-- **第 3 步预备**：A₅ 层 5-循环总数 = 24（5-循环全是偶置换，A₅ 与 S₅ 一致）。 -/
theorem G_fiveCycle_count : Nat.card {g : ↥G | g.val.cycleType = {5}} = 24 := by
  have h24 : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {5}} = 24 :=
    perm_fiveCycle_count
  rw [← h24]
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun g : {g : ↥G | g.val.cycleType = {5}} =>
      (⟨g.val.val, g.2⟩ : {h : Equiv.Perm (Fin 5) | h.cycleType = {5}}))
    ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : {h : Equiv.Perm (Fin 5) | h.cycleType = {5}} =>
      (x : Equiv.Perm (Fin 5))) hab
  · intro h
    have hsgn : h.val.sign = 1 := by
      rw [Equiv.Perm.sign_of_cycleType]
      rw [h.2]
      decide
    have hmem : h.val ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hsgn
    refine ⟨⟨⟨h.val, hmem⟩, h.2⟩, ?_⟩
    rfl

/-- **第 3 步推广**：任意 5-循环的中心化子 = ⟨g⟩。 -/
theorem G_centralizer_fiveCycle_eq_closure (g : G) (hg : g.val.cycleType = {5}) :
    Subgroup.centralizer ({g} : Set ↥G) = Subgroup.closure ({g} : Set ↥G) := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge
    (H := Subgroup.closure ({g} : Set ↥G))
    (K := Subgroup.centralizer ({g} : Set ↥G))
  · rw [Subgroup.closure_le]
    intro y hy
    rw [hy]
    change ∀ h ∈ ({g} : Set ↥G), h * g = g * h
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  · have hcl : Nat.card (Subgroup.closure ({g} : Set ↥G)) = 5 := by
      rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
      exact G_fiveCycle_orderOf g hg
    rw [hcl]
    let φ : Subgroup.centralizer ({g} : Set ↥G) →
        Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin 5))) :=
      fun x => ⟨(x : ↥G).val, by
        change ∀ h ∈ ({g.val} : Set (Equiv.Perm (Fin 5))), h * (x : ↥G).val = (x : ↥G).val * h
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        simpa [Subgroup.coe_mul] using congrArg Subtype.val (x.2 g (Set.mem_singleton g))⟩
    have hinj : Function.Injective φ := by
      intro a b hab
      have hv : (a : ↥G).val = (b : ↥G).val :=
        congrArg (fun y : Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin 5))) =>
          (y : Equiv.Perm (Fin 5))) hab
      apply Subtype.ext
      apply Subtype.ext
      exact hv
    calc Nat.card (Subgroup.centralizer ({g} : Set ↥G))
        ≤ Nat.card (Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin 5)))) :=
          Nat.card_le_card_of_injective _ hinj
      _ = 5 := by
          rw [Equiv.Perm.nat_card_centralizer, hg]
          norm_num

/-- **第 3 步推广**：任意 5-循环的类大小 = 12。 -/
theorem G_class_fiveCycle_card (g : G) (hg : g.val.cycleType = {5}) :
    Nat.card (ConjClasses.mk g).carrier = 12 := by
  haveI : Fintype ↥G := Fintype.ofFinite _
  haveI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (ConjAct ↥G) g) := Fintype.ofFinite _
  have hS : Fintype.card (MulAction.stabilizer (ConjAct ↥G) g) = 5 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    rw [G_centralizer_fiveCycle_eq_closure g hg]
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, G_fiveCycle_orderOf g hg]
  have hG : Fintype.card ↥G = 60 := by
    rw [← Nat.card_eq_fintype_card]; exact card_G
  have hcard : Fintype.card (ConjClasses.mk g).carrier = 12 := by
    rw [ConjClasses.card_carrier]; rw [hG]; rw [hS]
  rw [Nat.card_eq_fintype_card]
  exact hcard

/-- **第 3 步推广**：任意 5-循环所在共轭类集合的基数 = 12。 -/
theorem G_class_fiveCycle_set_card (g : G) (hg : g.val.cycleType = {5}) :
    Nat.card {h : ↥G | IsConj g h} = 12 := by
  have hset : ({h : ↥G | IsConj g h} : Set ↥G) = (ConjClasses.mk g).carrier := by
    ext h
    simp only [Set.mem_ofPred_eq]
    rw [← ConjAct.orbit_eq_carrier_conjClasses g]
    rw [ConjAct.mem_orbit_conjAct]
    exact isConj_comm
  rw [hset]
  exact G_class_fiveCycle_card g hg
/-- **第 3 步收口**：任意 `{5}`-型元素与 `sG` 或 `sG ^ 2` 共轭。 -/
theorem G_fiveCycle_isConj_sG (g : G) (hg : g.val.cycleType = {5}) :
    IsConj g sG ∨ IsConj g (sG ^ 2) := by
  have hsg : (sG.val : Equiv.Perm (Fin 5)).cycleType = {5} := by decide
  have hsg2 : (sG ^ 2 : G).val.cycleType = {5} := by native_decide
  have hA : Nat.card ({h : ↥G | IsConj sG h} : Set ↥G) = 12 := G_class_fiveCycle_set_card sG hsg
  have hB : Nat.card ({h : ↥G | IsConj (sG ^ 2) h} : Set ↥G) = 12 := G_class_fiveCycle_set_card (sG ^ 2) hsg2
  have hdisj : Disjoint ({h : ↥G | IsConj sG h} : Set ↥G)
      ({h : ↥G | IsConj (sG ^ 2) h} : Set ↥G) := by
    rw [Set.disjoint_left]
    intro h h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    exact sG_not_isConj_sG_sq (IsConj.trans h1 (IsConj.symm h2))
  have hEq : ({h : ↥G | h.val.cycleType = {5}} : Set ↥G)
      = {h : ↥G | IsConj sG h} ∪ {h : ↥G | IsConj (sG ^ 2) h} := by
    apply Eq.symm
    apply Set.eq_of_subset_of_ncard_le (ht := by exact Set.toFinite _)
    · intro h hh
      rw [Set.mem_union] at hh
      rcases hh with h1 | h1
      · simp only [Set.mem_ofPred_eq] at h1 ⊢
        obtain ⟨c, hc⟩ := h1
        have hv : IsConj (sG.val : Equiv.Perm (Fin 5)) h.val := by
          refine ⟨Units.map (Subgroup.subtype (alternatingGroup (Fin 5))) c, ?_⟩
          simpa [SemiconjBy, Subgroup.coe_mul, Units.coe_map] using congrArg Subtype.val hc
        rw [Equiv.Perm.isConj_iff_cycleType_eq] at hv
        rw [← hv, hsg]
      · simp only [Set.mem_ofPred_eq] at h1 ⊢
        obtain ⟨c, hc⟩ := h1
        have hv : IsConj ((sG ^ 2 : G).val : Equiv.Perm (Fin 5)) h.val := by
          refine ⟨Units.map (Subgroup.subtype (alternatingGroup (Fin 5))) c, ?_⟩
          simpa [SemiconjBy, Subgroup.coe_mul, Units.coe_map] using congrArg Subtype.val hc
        rw [Equiv.Perm.isConj_iff_cycleType_eq] at hv
        rw [← hv, hsg2]
    · rw [Set.ncard_union_eq hdisj (ht := by exact Set.toFinite _)]
      rw [show ({h : ↥G | IsConj sG h} : Set ↥G).ncard = 12 from
        (Nat.card_coe_set_eq _).symm.trans hA]
      rw [show ({h : ↥G | IsConj (sG ^ 2) h} : Set ↥G).ncard = 12 from
        (Nat.card_coe_set_eq _).symm.trans hB]
      rw [show ({h : ↥G | h.val.cycleType = {5}} : Set ↥G).ncard = 24 from
        (Nat.card_coe_set_eq _).symm.trans G_fiveCycle_count]
  have hgmem : g ∈ ({h : ↥G | h.val.cycleType = {5}} : Set ↥G) := hg
  rw [hEq] at hgmem
  rw [Set.mem_union] at hgmem
  rcases hgmem with h1 | h1
  · simp only [Set.mem_ofPred_eq] at h1
    exact Or.inl (IsConj.symm h1)
  · simp only [Set.mem_ofPred_eq] at h1
    exact Or.inr (IsConj.symm h1)

/-- **第 3 步**：S₅ 层 `{2,2}` 类大小 = 15（`120 / 8`）。 -/
theorem perm_twoTwo_count :
    Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}} = 15 := by
  have hrep : ((sG ^ 2 * tG : G).val : Equiv.Perm (Fin 5)).cycleType = {2,2} := by
    native_decide
  have h15 : Nat.card {h : Equiv.Perm (Fin 5) |
      IsConj ((sG ^ 2 * tG : G).val) h} = 15 := by
    rw [Equiv.Perm.card_isConj_eq, hrep]
    norm_num
  have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}}
      = {h : Equiv.Perm (Fin 5) | IsConj ((sG ^ 2 * tG : G).val) h} := by
    ext h
    simp only [Set.mem_ofPred_eq]
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hrep, eq_comm]
  rw [hset]
  exact h15

/-- **第 3 步**：A₅ 层 `{2,2}` 类大小 = 15（双换位全偶，故 A₅ 与 S₅ 的该类是同一批）。 -/
theorem G_twoTwo_set_card :
    Nat.card {g : ↥G | g.val.cycleType = {2,2}} = 15 := by
  have h15 : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}} = 15 := by
    have hrep : ((sG ^ 2 * tG : G).val : Equiv.Perm (Fin 5)).cycleType = {2,2} := by
      native_decide
    have h15' : Nat.card {h : Equiv.Perm (Fin 5) |
        IsConj ((sG ^ 2 * tG : G).val) h} = 15 := by
      rw [Equiv.Perm.card_isConj_eq, hrep]
      norm_num
    have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}}
        = {h : Equiv.Perm (Fin 5) | IsConj ((sG ^ 2 * tG : G).val) h} := by
      ext h
      simp only [Set.mem_ofPred_eq]
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hrep, eq_comm]
    rw [hset]
    exact h15'
  rw [← h15]
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun g : {g : ↥G | g.val.cycleType = {2,2}} =>
      (⟨g.val.val, g.2⟩ : {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}}))
    ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}} =>
      (x : Equiv.Perm (Fin 5))) hab
  · intro h
    have hsgn : h.val.sign = 1 := by
      rw [Equiv.Perm.sign_of_cycleType]
      rw [h.2]
      decide
    have hmem : h.val ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hsgn
    refine ⟨⟨⟨h.val, hmem⟩, h.2⟩, ?_⟩
    rfl

/-- **第 3 步**：S₅ 层 `{3}` 类大小 = 20（`120 / 6`）。 -/
theorem perm_threeCycle_count :
    Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {3}} = 20 := by
  have hrep : (tG.val : Equiv.Perm (Fin 5)).cycleType = {3} := by decide
  have h20 : Nat.card {h : Equiv.Perm (Fin 5) | IsConj tG.val h} = 20 := by
    rw [Equiv.Perm.card_isConj_eq, hrep]
    norm_num
  have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {3}}
      = {h : Equiv.Perm (Fin 5) | IsConj tG.val h} := by
    ext h
    simp only [Set.mem_ofPred_eq]
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hrep, eq_comm]
  rw [hset]
  exact h20

/-- **第 3 步**：A₅ 层 `{3}` 类大小 = 20（3-循环全偶，故 A₅ 与 S₅ 的该类是同一批）。 -/
theorem G_threeCycle_set_card :
    Nat.card {g : ↥G | g.val.cycleType = {3}} = 20 := by
  have h20 : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {3}} = 20 := by
    have hrep : (tG.val : Equiv.Perm (Fin 5)).cycleType = {3} := by decide
    have h20' : Nat.card {h : Equiv.Perm (Fin 5) | IsConj tG.val h} = 20 := by
      rw [Equiv.Perm.card_isConj_eq, hrep]
      norm_num
    have hset : {h : Equiv.Perm (Fin 5) | h.cycleType = {3}}
        = {h : Equiv.Perm (Fin 5) | IsConj tG.val h} := by
      ext h
      simp only [Set.mem_ofPred_eq]
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hrep, eq_comm]
    rw [hset]
    exact h20'
  rw [← h20]
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun g : {g : ↥G | g.val.cycleType = {3}} =>
      (⟨g.val.val, g.2⟩ : {h : Equiv.Perm (Fin 5) | h.cycleType = {3}}))
    ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : {h : Equiv.Perm (Fin 5) | h.cycleType = {3}} =>
      (x : Equiv.Perm (Fin 5))) hab
  · intro h
    have hsgn : h.val.sign = 1 := by
      rw [Equiv.Perm.sign_of_cycleType]
      rw [h.2]
      decide
    have hmem : h.val ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hsgn
    refine ⟨⟨⟨h.val, hmem⟩, h.2⟩, ?_⟩
    rfl

/-- 取逆保持共轭：IsConj g h → IsConj g⁻¹ h⁻¹。 -/
theorem IsConj_inv {g h : ↥G} (hh : IsConj g h) : IsConj (g⁻¹) (h⁻¹) := by
  obtain ⟨c, hc⟩ := hh
  refine IsConj.symm ⟨c⁻¹, ?_⟩
  show ((c⁻¹ : (↥G)ˣ) : ↥G) * h⁻¹ = g⁻¹ * ((c⁻¹ : (↥G)ˣ) : ↥G)
  have hkey : ((↑c : ↥G))⁻¹ * h⁻¹ = g⁻¹ * ((↑c : ↥G))⁻¹ := by
    calc ((↑c : ↥G))⁻¹ * h⁻¹ = (h * (↑c : ↥G))⁻¹ := by rw [← mul_inv_rev]
      _ = ((↑c : ↥G) * g)⁻¹ := by rw [← hc]
      _ = g⁻¹ * ((↑c : ↥G))⁻¹ := by rw [mul_inv_rev]
  simpa [Units.val_inv_eq_inv_val] using hkey

/-- χ(sG³) = α，即 tr(S³) = 1 + 2cos(2π/5) = α。 -/
theorem char_sG_cube : icosahedralRep.character (sG ^ 3) = alpha := by
  calc
    icosahedralRep.character (sG ^ 3) =
        LinearMap.trace ℂ (Fin 3 → ℂ) (ρG (sG ^ 3)) := by
      rw [icosahedralRep, FDRep.character, FDRep.of_ρ']
    _ = LinearMap.trace ℂ (Fin 3 → ℂ) (ρP (pA ^ 3)) := by
      congr 1
      calc
        ρG (sG ^ 3) = ρP (ψ (sG ^ 3)) := by simp [ρG]
        _ = ρP ((ψ sG) ^ 3) := by rw [map_pow]
        _ = ρP (pA ^ 3) := by rw [psi_sG]
    _ = ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 3).trace := by
      have hto : (Matrix.toLin' (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)) ^ 3
          = Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 3) := by
        rw [pow_succ]
        rw [pow_two]
        rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 3
            = (icosahedralS ^ 2) * icosahedralS from by rw [pow_succ]]
        rw [Matrix.toLin'_mul]
        rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 2
            = icosahedralS * icosahedralS from
              pow_two (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)]
        rw [Matrix.toLin'_mul]
        rfl
      rw [show ρP (pA ^ 3) =
          Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 3) from by
        rw [map_pow, ρP_pA_eq]
        rw [hto]]
      exact Matrix.trace_toLin'_eq _
    _ = alpha := by
      rw [pow_succ]
      rw [pow_two]
      unfold Matrix.trace
      simp [Matrix.mul_apply, Fin.sum_univ_succ, icosahedralS, c5, g5]
      unfold alpha
      ring_nf
      norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four]
      ring_nf


-- ========= 第 4 步（二）：五段求和 =========

/-- 恒等元这一段：只有 1 个元素，取值 3·3 = 9。 -/
theorem sum_zero_class :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = 0))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹) = 9 := by
  have hS1 : Finset.univ.filter (fun g : ↥G => g.val.cycleType = 0) = {1} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro h
      have hg : g = 1 := by
        apply Subtype.ext
        simpa using (Equiv.Perm.cycleType_eq_zero.mp h)
      rw [hg]
    · rintro h
      rw [h]
      show ((1 : ↥G).val : Equiv.Perm (Fin 5)).cycleType = 0
      exact Equiv.Perm.cycleType_one
  rw [hS1, Finset.sum_singleton]
  rw [inv_one, char_one]
  norm_num

/-- {3} 这一段：χ 恒为 0，整段求和为 0。 -/
theorem sum_three_class :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {3}))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹) = 0 := by
  rw [Finset.sum_eq_zero]
  intro g hg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
  have hconj : IsConj g tG := G_threeCycle_isConj g hg
  have hchi : icosahedralRep.character g = 0 := by
    have h := char_eq_of_isConj tG g (IsConj.symm hconj)
    rwa [char_tG] at h
  rw [hchi, zero_mul]

/-- {2,2} 这一段：15 个元素，每个取值 (−1)·(−1) = 1。 -/
theorem sum_two_two_class :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {2, 2}))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹) = 15 := by
  have hc : ∀ g ∈ Finset.univ.filter (fun g : ↥G => g.val.cycleType = {2, 2}),
      icosahedralRep.character g * icosahedralRep.character g⁻¹ = 1 := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have hg2 : g ^ 2 = 1 := by
      have ho : orderOf (g.val : Equiv.Perm (Fin 5)) = 2 := by
        rw [← Equiv.Perm.lcm_cycleType, hg]
        simp
      have ho2 : orderOf g = 2 := by rwa [← Subgroup.orderOf_coe]
      rw [← ho2]
      exact pow_orderOf_eq_one g
    have hginv : g⁻¹ = g := by
      have h2 : g * g = 1 := by rw [← pow_two]; exact hg2
      exact inv_eq_of_mul_eq_one_left h2
    have hconj : IsConj g (sG ^ 2 * tG) := G_twoTwo_isConj g hg
    have hchi : icosahedralRep.character g = -1 := by
      have h := char_eq_of_isConj (sG ^ 2 * tG) g (IsConj.symm hconj)
      rwa [char_sG_sq_tG] at h
    rw [hginv, hchi]
    norm_num
  rw [Finset.sum_congr rfl hc, Finset.sum_const]
  have hcard :
      (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {2, 2})).card = 15 := by
    have h1 : Nat.card {g : ↥G | g.val.cycleType = {2, 2}} = 15 := G_twoTwo_set_card
    have h2 : Fintype.card {g : ↥G // g.val.cycleType = {2, 2}} = 15 := by
      rwa [Nat.card_eq_fintype_card] at h1
    rw [← Fintype.card_subtype]
    exact h2
  rw [hcard]
  norm_num

/-- 共轭保持 cycleType：A₅ 内共轭的两元素 cycleType 相同。 -/
theorem G_isConj_cycleType (g h : ↥G) (hh : IsConj g h) :
    h.val.cycleType = g.val.cycleType := by
  obtain ⟨c, hc⟩ := hh
  have hcy : h = (↑c : ↥G) * g * (↑c : ↥G)⁻¹ := by
    have h1 : h * (↑c : ↥G) * (↑c : ↥G)⁻¹ = h := by
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have h2 : h * (↑c : ↥G) * (↑c : ↥G)⁻¹ = (↑c : ↥G) * g * (↑c : ↥G)⁻¹ := by
      rw [← hc]
    exact h1.symm.trans h2
  have hperm : (h.val : Equiv.Perm (Fin 5))
      = ((↑c : ↥G).val) * g.val * ((↑c : ↥G).val)⁻¹ := by
    conv_lhs => rw [hcy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hperm, Equiv.Perm.cycleType_conj]

theorem sG_pow_eq_one : sG ^ 5 = 1 := by
  have := pow_orderOf_eq_one sG
  rwa [orderOf_sG] at this

theorem sG_inv_eq_pow_four : sG⁻¹ = sG ^ 4 := by
  have h4 : sG ^ 4 * sG = 1 := by rw [← pow_succ, sG_pow_eq_one]
  exact inv_eq_of_mul_eq_one_left h4

theorem sG_val_cycleType : sG.val.cycleType = {5} := by decide

/-- {5} 类 A 段（与 sG 共轭）：12 个，每项 ᾱ² = 2 − α。 -/
theorem sum_five_a :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹)
      = 12 * (2 - alpha) := by
  classical
  have hkey : (1 - alpha) * (1 - alpha) = 2 - alpha := by
    calc (1 - alpha) * (1 - alpha) = 1 - 2 * alpha + alpha * alpha := by ring
      _ = 1 - 2 * alpha + (1 + alpha) := by rw [alpha_sq]
      _ = 2 - alpha := by ring
  have hc : ∀ g ∈ Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG),
      icosahedralRep.character g * icosahedralRep.character g⁻¹ = 2 - alpha := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨_, hconj⟩ := hg
    have h1 : icosahedralRep.character g = 1 - alpha := by
      have h := char_eq_of_isConj sG g (IsConj.symm hconj)
      rwa [char_sG] at h
    have h2 : icosahedralRep.character g⁻¹ = 1 - alpha := by
      have hinv : IsConj (g⁻¹) (sG⁻¹) := IsConj_inv hconj
      have h := char_eq_of_isConj (sG⁻¹) (g⁻¹) (IsConj.symm hinv)
      rwa [char_sG_inv] at h
    rw [h1, h2, hkey]
  rw [Finset.sum_congr rfl hc, Finset.sum_const]
  have hcard :
      (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG)).card = 12 := by
    have hset : {g : ↥G | g.val.cycleType = {5} ∧ IsConj g sG} = {g : ↥G | IsConj sG g} := by
      ext g
      change (g.val.cycleType = {5} ∧ IsConj g sG) ↔ IsConj sG g
      constructor
      · rintro ⟨_, hc⟩
        exact IsConj.symm hc
      · intro hc
        have hg5 : g.val.cycleType = {5} := by
          rw [G_isConj_cycleType sG g hc, sG_val_cycleType]
        exact ⟨hg5, IsConj.symm hc⟩
    have h1 : Nat.card {g : ↥G | g.val.cycleType = {5} ∧ IsConj g sG} = 12 := by
      rw [hset]
      exact G_class_fiveCycle_set_card sG sG_val_cycleType
    have h2 : Fintype.card {g : ↥G // g.val.cycleType = {5} ∧ IsConj g sG} = 12 := by
      rwa [Nat.card_eq_fintype_card] at h1
    rw [← Fintype.card_subtype]
    exact h2
  rw [hcard]
  norm_num

theorem sG_sq_val_cycleType : ((sG ^ 2 : ↥G).val : Equiv.Perm (Fin 5)).cycleType = {5} := by
  native_decide

theorem sG_sq_inv_eq_cube : ((sG ^ 2 : ↥G))⁻¹ = sG ^ 3 := by
  rw [← inv_pow, sG_inv_eq_pow_four, ← pow_mul]
  rw [show (4 * 2 : ℕ) = 3 + 5 from by norm_num, pow_add, sG_pow_eq_one, mul_one]

/-- {5} 类 B 段（与 sG² 共轭）：12 个，每项 α² = 1 + α。 -/
theorem sum_five_b :
    Finset.sum (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)))
      (fun g => icosahedralRep.character g * icosahedralRep.character g⁻¹)
      = 12 * (1 + alpha) := by
  classical
  have hc : ∀ g ∈ Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)),
      icosahedralRep.character g * icosahedralRep.character g⁻¹ = 1 + alpha := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨_, hconj⟩ := hg
    have h1 : icosahedralRep.character g = alpha := by
      have h := char_eq_of_isConj (sG ^ 2) g (IsConj.symm hconj)
      rwa [char_sG_sq] at h
    have h2 : icosahedralRep.character g⁻¹ = alpha := by
      have hinv : IsConj (g⁻¹) ((sG ^ 2)⁻¹) := IsConj_inv hconj
      rw [sG_sq_inv_eq_cube] at hinv
      have h := char_eq_of_isConj (sG ^ 3) (g⁻¹) (IsConj.symm hinv)
      rwa [char_sG_cube] at h
    rw [h1, h2, alpha_sq]
  rw [Finset.sum_congr rfl hc, Finset.sum_const]
  have hcard :
      (Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2))).card = 12 := by
    have hset : {g : ↥G | g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)}
        = {g : ↥G | IsConj (sG ^ 2) g} := by
      ext g
      change (g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)) ↔ IsConj (sG ^ 2) g
      constructor
      · rintro ⟨_, hc⟩
        exact IsConj.symm hc
      · intro hc
        have hg5 : g.val.cycleType = {5} := by
          rw [G_isConj_cycleType (sG ^ 2) g hc, sG_sq_val_cycleType]
        exact ⟨hg5, IsConj.symm hc⟩
    have h1 : Nat.card {g : ↥G | g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)} = 12 := by
      rw [hset]
      exact G_class_fiveCycle_set_card (sG ^ 2) sG_sq_val_cycleType
    have h2 : Fintype.card {g : ↥G // g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)} = 12 := by
      rwa [Nat.card_eq_fintype_card] at h1
    rw [← Fintype.card_subtype]
    exact h2
  rw [hcard]
  ring


-- ========= 第 4 步（三）：总装 =========

/-- **第 4 步（三）**：不可约判据的和 —— `∑ g, χ(g)χ(g⁻¹) = 60 = |A₅|`。

五段拆分：`{1}` 9、`{3}` 0、`{2,2}` 15、`{5}A` 12(2−α)、`{5}B` 12(1+α)，
合计 `24 + 12·3 = 60`。 -/
theorem icosahedral_char_sum :
    Finset.sum (Finset.univ : Finset ↥G)
      (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹) = 60 := by
  classical
  -- 逐层拆分：p1 = {1}、p2 = {3}、p3 = {2,2}、p4 = {5}A、p5 = {5}B
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ↥G)
    (fun g : ↥G => g.val.cycleType = 0)
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0))
    (fun g : ↥G => g.val.cycleType = {3})
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  rw [← Finset.sum_filter_add_sum_filter_not
    (((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3}))
    (fun g : ↥G => g.val.cycleType = {2, 2})
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2}))
    (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG)
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  rw [← Finset.sum_filter_add_sum_filter_not
    (((((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2})).filter
      (fun g : ↥G => ¬ (g.val.cycleType = {5} ∧ IsConj g sG)))
    (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2))
    (fun g : ↥G => icosahedralRep.character g * icosahedralRep.character g⁻¹)]
  -- 桥接：累积 filter 化回裸 filter（`filter_filter` 右结合）
  have hb2 : (Finset.univ.filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => g.val.cycleType = {3})
      = Finset.univ.filter (fun g : ↥G => g.val.cycleType = {3}) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro h; exact h.2
    · intro h
      exact ⟨by rw [h]; decide, h⟩
  have hb3 : ((Finset.univ.filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => g.val.cycleType = {2, 2})
      = Finset.univ.filter (fun g : ↥G => g.val.cycleType = {2, 2}) := by
    rw [Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro h; exact h.2.2
    · intro h
      exact ⟨by rw [h]; decide, ⟨by rw [h]; decide, h⟩⟩
  have hb4 : (((Finset.univ.filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2})).filter
      (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG)
      = Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g sG) := by
    rw [Finset.filter_filter, Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro h; exact h.2.2.2
    · intro h
      exact ⟨by rw [h.1]; decide, ⟨by rw [h.1]; decide, ⟨by rw [h.1]; decide, h⟩⟩⟩
  have hb5 : ((((Finset.univ.filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2})).filter
      (fun g : ↥G => ¬ (g.val.cycleType = {5} ∧ IsConj g sG))).filter
      (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2))
      = Finset.univ.filter (fun g : ↥G => g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)) := by
    rw [Finset.filter_filter, Finset.filter_filter, Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro g _
    constructor
    · intro h; exact h.2.2.2.2
    · intro h
      refine ⟨by rw [h.1]; decide, ⟨by rw [h.1]; decide,
        ⟨by rw [h.1]; decide, ⟨?_, h⟩⟩⟩⟩
      intro hh
      exact sG_not_isConj_sG_sq (IsConj.trans (IsConj.symm hh.2) h.2)
  -- 末段为空：五段已覆盖全部 60 元
  have hempty : (((((Finset.univ : Finset ↥G).filter (fun g : ↥G => ¬ g.val.cycleType = 0)).filter
      (fun g : ↥G => ¬ g.val.cycleType = {3})).filter
      (fun g : ↥G => ¬ g.val.cycleType = {2, 2})).filter
      (fun g : ↥G => ¬ (g.val.cycleType = {5} ∧ IsConj g sG))).filter
      (fun g : ↥G => ¬ (g.val.cycleType = {5} ∧ IsConj g (sG ^ 2))) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have h1 : ¬ g.val.cycleType = 0 := hg.1.1.1.1
    have h2 : ¬ g.val.cycleType = {3} := hg.1.1.1.2
    have h3 : ¬ g.val.cycleType = {2, 2} := hg.1.1.2
    have h4 : ¬ (g.val.cycleType = {5} ∧ IsConj g sG) := hg.1.2
    have h5 : ¬ (g.val.cycleType = {5} ∧ IsConj g (sG ^ 2)) := hg.2
    rcases G_cycleType_cases g with hc | hc | hc | hc
    · exact h1 hc
    · exact h2 hc
    · rcases G_fiveCycle_isConj_sG g hc with hcs | hcs
      · exact h4 ⟨hc, hcs⟩
      · exact h5 ⟨hc, hcs⟩
    · exact h3 hc
  rw [hb2, hb3, hb4, hb5, hempty, Finset.sum_empty]
  rw [sum_zero_class, sum_three_class, sum_two_two_class, sum_five_a, sum_five_b]
  ring
