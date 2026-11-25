import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.ToLin
import OrderPreservingBijection.QuadraticFieldFive

/-!
# A₅ 的 3 维不可约表示（二十面体表示）

本文件是"结理论 ↔ χ₅ 域"桥的 Lean 侧骨架。

- 结理论侧：正十二面体 / 二十面体五重对称 → 黄金比 φ。
- 数论侧：Q(√5) = χ₅ 的算术域；GoldenInt = ℤ[φ]（已在我们库里，
  含 phi_sq / phi_mul_phi_bar / phi_add_phi_bar）。

核心数学事实（实现路径，逐击破清单）：

1. 生成元：A₅ 由 3-循环生成（mathlib: closure_three_cycles_eq_alternating）。
2. 群同态构造（PresentedGroup 路线，本轮已定案）：
   - A₅ ≅ ⟨s, t | s³ = t⁵ = (st)² = 1⟩（s = 3 阶元如 (123)，t = 5 阶元如 (12345)）。
   - P := PresentedGroup rels（mathlib Mathlib/GroupTheory/PresentedGroup.lean）。
   - φ : P →* alternatingGroup (Fin 5)：toGroup，置换关系（decidable 验证）。
   - ψ : P →* GL₃ ℂ：toGroup，旋转矩阵关系（符号验证）。
   - 呈现完整性（ker φ = normalClosure rels，即 |P| = 60）：深水区，
     需证明 A₅ 的呈现定理——这是 #2 的最后一块硬骨头。
3. 显式矩阵：绕 z 轴 2π/3（3 阶）与绕 5 重轴 2π/5（5 阶）的旋转；
   用 Rz(θ)ⁿ = Rz(nθ)（sin_nat_mul_pi / cos_nat_mul_pi 周期论证）验证幂关系；
   cos(2π/5) = (√5-1)/4 由 mathlib cos_pi_div_five + 倍角公式。
4. 不可约性：FDRep.simple_iff_char_is_norm_one（FinGroupCharZero.lean:120）：
   Simple V ↔ ∑ g, χ(g)·χ(g⁻¹) = |G| = 60。按共轭类求和：
   χ(1)=3, χ(2A)=-1, χ(3A)=0, χ(5A)=φ, χ(5B)=φ̄=1-φ（共轭类大小
   1,15,20,12,12），范数 = 9·1 + 1·15 + 0·20 + (φ²+φ̄²)·12
          = 9 + 15 + (φ+φ̄+2)·12 = 9 + 15 + 3·12 = 60 ✓
5. 5 阶元特征标值：tr R_z(2π/5) = 1 + 2cos(2π/5) = 1 + (√5-1)/2 = φ。
6. 特征标值 ∈ Q(√5)：候选值 {3, -1, 0, φ, φ̄} 全在 goldenToComplex 像里
   （本轮已完成代数骨架：goldenToComplex_phi / _three / _neg_one / _zero / _phi_bar）。
-/

noncomputable section

open Representation

/-- A₅ = 交替群 acting on Fin 5。 -/
abbrev G := alternatingGroup (Fin 5)

/-- 黄金比在 ℂ 中的像：α = (1+√5)/2。 -/
noncomputable def alpha : ℂ := (1 + (Real.sqrt 5 : ℂ)) / 2

/-- α² = 1 + α，即 α 满足 ω 的方程（φ² = φ + 1）。 -/
lemma alpha_sq : alpha * alpha = 1 + alpha := by
  unfold alpha
  have hsC : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    have h : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    exact_mod_cast h
  field_simp
  ring_nf
  rw [hsC]
  ring

/-- 黄金整数环 ℤ[φ] → ℂ 的嵌入：φ ↦ (1+√5)/2。
    由 QuadraticAlgebra.lift 泛性质给出（验证 (1+√5)/2 满足 x² - x - 1 = 0）。 -/
noncomputable def goldenToComplex : GoldenInt →ₐ[ℤ] ℂ :=
  QuadraticAlgebra.lift ⟨alpha, by simpa using alpha_sq⟩

/- ======================================================================== -/
-- #6 的代数骨架：特征标候选值 {3, -1, 0, φ, φ̄} 全部落在 goldenToComplex 的像
-- （即 Q(√5)）中。此部分独立于 icosahedralRep 的构造，先完成。
/- ======================================================================== -/

/-- goldenToComplex 把 φ 送到 α = (1+√5)/2。 -/
lemma goldenToComplex_phi : goldenToComplex GoldenInt.phi = alpha := by
  rw [goldenToComplex]
  simp [alpha, GoldenInt.phi]

/-- 3 = goldenToComplex 3。 -/
lemma goldenToComplex_three : goldenToComplex (3 : GoldenInt) = (3 : ℂ) := by
  exact map_natCast goldenToComplex 3

/-- -1 = goldenToComplex (-1)。 -/
lemma goldenToComplex_neg_one : goldenToComplex (-1 : GoldenInt) = (-1 : ℂ) := by
  rw [map_neg, map_one]

/-- 0 = goldenToComplex 0。 -/
lemma goldenToComplex_zero : goldenToComplex (0 : GoldenInt) = 0 := by
  exact map_zero goldenToComplex

/-- φ̄ = 1 - φ 的像 = 1 - α（ℂ 中的共轭黄金比）。 -/
lemma goldenToComplex_phi_bar : goldenToComplex GoldenInt.phi_bar = 1 - alpha := by
  rw [GoldenInt.phi_bar_eq, map_sub, map_one, goldenToComplex_phi]

/- ======================================================================== -/
-- #2 生成元：s = (0 1 2 3 4)，t = (0 1 2)；closure {s, t} = A₅
--
-- 数学路线（阶论证）：
--   H := closure {sG, tG} ⊆ A₅。
--   3 | |H|（t 的阶 = 3）、5 | |H|（s 的阶 = 5）→ 15 | |H|；
--   |H| | |A₅| = 60（Lagrange，card_subgroup_dvd_card）。
--   排除 |H| = 30：指数 2 子群正规（normal_of_index_eq_two）→
--     A₅ 单群（isSimpleGroup_five）矛盾。
--   排除 |H| = 15：指数 4 → 陪集作用同态 f : A₅ →* Perm(A₅/H)；
--     核 = normalCore H（normalCore_eq_ker）——核平凡则单射，|A₅| ≤ 4! = 24 矛盾；
--     核非平凡则 normalCore = ⊤（单群）→ H = ⊤ 矛盾。
--   → |H| = 60 = |A₅| → H = ⊤（基数相等 + toFinset）。
/- ======================================================================== -/

open Equiv.Perm

-- orderOf_eq_prime 需要素数的 Fact 实例（仅本文件有效）
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- s = (0 1 2 3 4)：Fin 5 上的 5 循环。 -/
def s : Equiv.Perm (Fin 5) := List.formPerm [0, 1, 2, 3, 4]

/-- t = (0 1 2)：Fin 5 上的 3 循环。 -/
def t : Equiv.Perm (Fin 5) := List.formPerm [0, 1, 2]

/-- t 是 3 循环（cycleType = {3}）。 -/
lemma t_is_three_cycle : IsThreeCycle t := by
  rw [← card_support_eq_three_iff]
  rw [t]
  rw [List.support_formPerm_of_nodup ([0, 1, 2] : List (Fin 5)) (by decide : ([0, 1, 2] : List (Fin 5)).Nodup)]
  · decide
  · intro x hx
    simp at hx

/-- s 是循环（5 循环）。 -/
lemma s_is_cycle : IsCycle s := by
  simpa [s] using List.isCycle_formPerm (by decide : ([0, 1, 2, 3, 4] : List (Fin 5)).Nodup)
    (by norm_num : 2 ≤ ([0, 1, 2, 3, 4] : List (Fin 5)).length)

/-- sign t = 1，故 t ∈ A₅。 -/
lemma t_sign : Equiv.Perm.sign t = 1 := t_is_three_cycle.sign

/-- sign s = 1，故 s ∈ A₅。 -/
lemma s_sign : Equiv.Perm.sign s = 1 := by
  rw [s]
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

/-- s, t 作为 A₅ 的元素。 -/
def sG : G := ⟨s, mem_alternatingGroup.mpr s_sign⟩

/-- t 作为 A₅ 的元素。 -/
def tG : G := ⟨t, mem_alternatingGroup.mpr t_sign⟩

/-- t 的阶 = 3。 -/
lemma orderOf_tG : orderOf tG = 3 := by
  apply orderOf_eq_prime
  · change tG ^ 3 = 1
    have ht : t ^ 3 = 1 := by
      simpa [t_is_three_cycle.orderOf] using pow_orderOf_eq_one t
    simp [tG, ht]
  · intro h
    apply t_is_three_cycle.ne_one
    exact congrArg Subtype.val h

/-- s 的阶 = 5。 -/
lemma orderOf_sG : orderOf sG = 5 := by
  apply orderOf_eq_prime
  · change sG ^ 5 = 1
    have hs : s ^ 5 = 1 := by
      apply Equiv.ext
      intro x
      fin_cases x <;> decide
    simp [sG, hs]
  · intro h
    have hs0 : s 0 = 1 := by decide
    have hs0' : s 0 = 0 := by
      have hs_eq : s = 1 := by exact congrArg Subtype.val h
      simpa using congrArg (fun e : Equiv.Perm (Fin 5) => e 0) hs_eq
    rw [hs0] at hs0'
    norm_num at hs0'

/-- |A₅| = 60。 -/
lemma card_G : Nat.card G = 60 := by
  have htwo := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_perm] at htwo
  norm_num at htwo ⊢
  omega

/-- H := closure {sG, tG}。 -/
abbrev SGen := Subgroup.closure ({sG, tG} : Set G)

/-- 子群元素 ⟨tG, _⟩ 的阶 = 3（群中阶 3 的元素的子群内阶仍为 3）。 -/
lemma orderOf_mem_tG : ∀ {htmem : tG ∈ SGen}, orderOf (⟨tG, htmem⟩ : SGen) = 3 := by
  intro htmem
  apply orderOf_eq_prime
  · have ht : tG ^ 3 = 1 := by
      have : tG ^ orderOf tG = 1 := pow_orderOf_eq_one tG
      simpa [orderOf_tG] using this
    simpa using ht
  · intro h
    apply t_is_three_cycle.ne_one
    exact Subtype.mk.inj (Subtype.mk.inj h)

/-- 3 | |closure {sG, tG}|。 -/
lemma three_dvd_card_SGen : 3 ∣ Nat.card SGen := by
  have htmem : tG ∈ SGen := by
    apply Subgroup.subset_closure
    simpa using (Set.subset_insert (s := ({tG} : Set G)) (a := sG)) (by exact Or.inl rfl)
  have hd : orderOf (⟨tG, htmem⟩ : SGen) ∣ Nat.card SGen :=
    orderOf_dvd_of_pow_eq_one (pow_card_eq_one' (G := SGen) (x := ⟨tG, htmem⟩))
  rw [orderOf_mem_tG] at hd
  exact hd

/-- 子群元素 ⟨sG, _⟩ 的阶 = 5（群中阶 5 的元素的子群内阶仍为 5）。 -/
lemma orderOf_mem_sG : ∀ {hsmem : sG ∈ SGen}, orderOf (⟨sG, hsmem⟩ : SGen) = 5 := by
  intro hsmem
  apply orderOf_eq_prime
  · have hs : s ^ 5 = 1 := by
      apply Equiv.ext
      intro x
      fin_cases x <;> decide
    simpa [sG, hs]
  · intro h
    have hs0 : s 0 = 1 := by decide
    have hs0' : s 0 = 0 := by
      have hs_eq : s = 1 := by
        exact Subtype.mk.inj (Subtype.mk.inj h)
      simpa using congrArg (fun e : Equiv.Perm (Fin 5) => e 0) hs_eq
    rw [hs0] at hs0'
    norm_num at hs0'

/-- 5 | |closure {sG, tG}|。 -/
lemma five_dvd_card_SGen : 5 ∣ Nat.card SGen := by
  have hsmem : sG ∈ SGen := by
    apply Subgroup.subset_closure
    simpa using (Set.subset_insert (s := ({sG} : Set G)) (a := tG)) (by exact Or.inl rfl)
  have hd : orderOf (⟨sG, hsmem⟩ : SGen) ∣ Nat.card SGen :=
    orderOf_dvd_of_pow_eq_one (pow_card_eq_one' (G := SGen) (x := ⟨sG, hsmem⟩))
  rw [orderOf_mem_sG] at hd
  exact hd

/-- 15 | |closure {sG, tG}|。 -/
lemma fifteen_dvd_card_SGen : 15 ∣ Nat.card SGen := by
  rcases three_dvd_card_SGen with ⟨k, hk⟩
  have h5k : 5 ∣ k := by
    have h5' : 5 ∣ 3 * k := by simpa [hk] using five_dvd_card_SGen
    exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime 5 3)
      (by simpa [mul_comm] using h5'))
  rcases h5k with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  rw [hk, hm]
  ring

/-- closure {sG, tG} = ⊤：s, t 生成 A₅。
路线：15 | |H|（t 阶 3、s 阶 5），|H| | 60（Lagrange），故 |H| ∈ {15, 30, 60}。
排除 30：指数 2 子群正规（normal_of_index_eq_two），与 A₅ 单群矛盾；
排除 15：指数 4 的陪集作用 f : G →* Perm (G/H)，核 = normalCore H
  —— 核平凡则 f 单射，60 ≤ 4! 矛盾；核非平凡则 normalCore = ⊤（单群），H = ⊤ 矛盾；
剩下 |H| = 60 = |G|，指数 1 推出 H = ⊤。 -/
lemma closure_eq_top : SGen = ⊤ := by
  have hdiv : Nat.card SGen ∣ 60 := by
    have h := Subgroup.card_subgroup_dvd_card SGen
    rw [card_G] at h
    exact h
  have h15 : 15 ∣ Nat.card SGen := fifteen_dvd_card_SGen
  rcases h15 with ⟨k, hk⟩
  have hk_le : k ≤ 4 := by
    have : 15 * k ≤ 60 := Nat.le_of_dvd (by norm_num : 0 < 60) (by simpa [hk] using hdiv)
    omega
  have hk_pos : 1 ≤ k := by
    have hk_dvd : 15 * k ∣ 60 := by simpa [hk] using hdiv
    have hpos : 0 < 15 * k := Nat.pos_of_dvd_of_pos hk_dvd (by norm_num : 0 < 60)
    have h15le : 15 ≤ 15 * k := Nat.le_of_dvd hpos ⟨k, rfl⟩
    omega
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    interval_cases k <;> simp_all
  rcases hcases with hk1 | hk2 | hk3 | hk4
  · -- k = 1：|H| = 15 → 排除（指数 4 陪集作用）
    exfalso
    have hn : Nat.card SGen = 15 := by omega
    have hindex : SGen.index = 4 := by
      have hprod : SGen.index * Nat.card SGen = 60 := by
        rw [← card_G]
        exact Subgroup.index_mul_card (H := SGen)
      rw [hn] at hprod
      omega
    let f : G →* Equiv.Perm (G ⧸ SGen) := MulAction.toPermHom G (G ⧸ SGen)
    have hker : f.ker = SGen.normalCore := by
      exact (Subgroup.normalCore_eq_ker (H := SGen)).symm
    by_cases hbot : f.ker = ⊥
    · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hbot
      have hcard : Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ SGen)) :=
        Nat.card_le_card_of_injective f hinj
      rw [card_G, Nat.card_perm, ← Subgroup.index_eq_card, hindex] at hcard
      norm_num at hcard
    · have hnc_ne_bot : SGen.normalCore ≠ ⊥ := by
        simpa [hker] using hbot
      have hsimple : SGen.normalCore = ⊥ ∨ SGen.normalCore = ⊤ :=
        IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := G) SGen.normalCore SGen.normalCore_normal
      have htop_nc : SGen.normalCore = ⊤ := by
        rcases hsimple with h | h
        · exact False.elim (hnc_ne_bot h)
        · exact h
      have hSGen : SGen = ⊤ := by
        apply le_antisymm
        · simp
        · simpa [htop_nc] using (SGen.normalCore_le)
      have : Nat.card SGen = 60 := by
        rw [hSGen, Subgroup.card_top, card_G]
      omega
  · -- k = 2：|H| = 30 → 排除（指数 2 正规 + 单群矛盾）
    exfalso
    have hn : Nat.card SGen = 30 := by omega
    have hindex : SGen.index = 2 := by
      have hprod : SGen.index * Nat.card SGen = 60 := by
        rw [← card_G]
        exact Subgroup.index_mul_card (H := SGen)
      rw [hn] at hprod
      omega
    have hnormal : SGen.Normal := Subgroup.normal_of_index_eq_two hindex
    have hsimple : SGen = ⊥ ∨ SGen = ⊤ :=
      IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := G) SGen hnormal
    rcases hsimple with hbot | htop
    · have hcard1 : Nat.card SGen = 1 := by simpa [hbot]
      have h15le : 15 ≤ Nat.card SGen := by omega
      omega
    · have : Nat.card SGen = 60 := by
        rw [htop, Subgroup.card_top, card_G]
      omega
  · -- k = 3：45 | 60 矛盾
    exfalso
    have : 45 ∣ 60 := by simpa [hk, hk3] using hdiv
    norm_num at this
  · -- k = 4：|H| = 60 = |G| → 指数 1 → H = ⊤
    have hn : Nat.card SGen = 60 := by omega
    have hindex : SGen.index = 1 := by
      have hprod : SGen.index * Nat.card SGen = 60 := by
        rw [← card_G]
        exact Subgroup.index_mul_card (H := SGen)
      rw [hn] at hprod
      omega
    exact (Subgroup.index_eq_one.mp hindex)

/- ======================================================================== -/
-- #3：二十面体表示 icosahedralRep（PresentedGroup 路线，本轮定案）
--
-- 数学路线：
--   P := ⟨s, t | s⁵ = t³ = (st)² = 1⟩（s = 5 阶元 (12345)，t = 3 阶元 (123)）。
--   φ : P →* G（s ↦ sG, t ↦ tG）：满射（由 closure_eq_top 推出）。
--   ψ : P →* GL₃ ℂ（s ↦ S, t ↦ T，S⁵ = T³ = (ST)² = I）。
--   ρ : G →* GL₃ ℂ := 因子化 ψ 过 φ（需呈现完整 |P| = 60）。
--   icosahedralRep := FDRep.of ρ（V := Fin 3 → ℂ）；finrank = 3。
--
-- 子任务分解：
--   #3a（本段）：rels / P / st_sq / φ（满射）。
--   #3b：显式矩阵 S、T + ψ（矩阵关系验证）。
--   #3c：呈现完整性 |P| = 60（深水区）。
--   #3d：因子化 ρ + FDRep.of + finrank。
/- ======================================================================== -/

/-- 呈现关系：s⁵ = t³ = (s²t)² = 1。
    注：s=(12345) 与 t=(123) 的乘积 st = (0 2 1 3 4) 是 5 阶元（不是 2 阶），
    但 s²·t = (0 3)(1 4) 是双对换（2 阶）；⟨s², t⟩ = ⟨s, t⟩ = A₅（s = (s²)³），
    故经典呈现 a⁵ = b³ = (ab)² = 1（a = s²、b = t）翻译到 s、t 即 s⁵ = t³ = (s²t)² = 1。 -/
def rels : Set (FreeGroup (Fin 2)) :=
  { (FreeGroup.of 0) ^ 5, (FreeGroup.of 1) ^ 3, ((FreeGroup.of 0) ^ 2 * (FreeGroup.of 1)) ^ 2 }

/-- P := ⟨s, t | s⁵ = t³ = (s²t)² = 1⟩。 -/
abbrev P := PresentedGroup rels

/-- (sG² · tG)² = 1：s²·t = (0 3)(1 4) 是双对换（2 阶元）。 -/
lemma s2t_sq : (sG ^ 2 * tG) ^ 2 = 1 := by
  apply Subtype.ext
  change (s ^ 2 * t) ^ 2 = 1
  apply Equiv.ext
  intro x
  fin_cases x <;> decide

/-- φ : P →* G，s ↦ sG、t ↦ tG。 -/
def φ : P →* G :=
  PresentedGroup.toGroup (f := fun i : Fin 2 => if i = 0 then sG else tG) (by
    intro r hr
    simp [rels] at hr
    rcases hr with rfl | rfl | rfl
    · change FreeGroup.lift (fun i : Fin 2 => if i = 0 then sG else tG) ((FreeGroup.of 0) ^ 5) = 1
      simp
      have hs : sG ^ 5 = 1 := by
        have := pow_orderOf_eq_one sG
        rwa [orderOf_sG] at this
      exact hs
    · change FreeGroup.lift (fun i : Fin 2 => if i = 0 then sG else tG) ((FreeGroup.of 1) ^ 3) = 1
      simp
      have ht : tG ^ 3 = 1 := by
        have := pow_orderOf_eq_one tG
        rwa [orderOf_tG] at this
      exact ht
    · change FreeGroup.lift (fun i : Fin 2 => if i = 0 then sG else tG) (((FreeGroup.of 0) ^ 2 * (FreeGroup.of 1)) ^ 2) = 1
      simp
      exact s2t_sq
  )

/-- φ 满射：closure {sG, tG} = ⊤ → range φ = ⊤。 -/
lemma φ_range_top : φ.range = ⊤ := by
  apply le_antisymm
  · exact le_top
  · rw [← closure_eq_top]
    rw [Subgroup.closure_le]
    intro x hx
    simp at hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨PresentedGroup.of 0, by simp [φ]⟩
    · rw [hx]
      exact ⟨PresentedGroup.of 1, by simp [φ]⟩

/- ======================================================================== -/
-- #3b 显式矩阵 S、T + ψ : P →* (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)
--
-- 数学（数值已验证，见 build_step3 前的 Python 检查）：
--   T = 绕 3 重轴 (1,1,1) 2π/3 = 循环置换 [[0,0,1],[1,0,0],[0,1,0]]（纯整数，迹 0）。
--   A = 绕 5 重轴 (0,1,φ) 2π/5，干净形式全 ∈ Q(√5)：
--     A = [[c, -g, 1/2], [g, 1/2, c], [-1/2, c, g]]，c = cos72° = (√5-1)/4、g = φ/2 = (1+√5)/4。
--   S := A³（ψ(s)，5 阶，迹 = φ̄ = (1-√5)/2）：
--     S = [[-g, 1/2, -c], [-1/2, -c, g], [c, g, 1/2]]。
--   验证：S⁵ = A¹⁵ = I、T³ = I、(S²T)² = (A⁶T)² = (AT)² = I。
--   对应：ψ(s) = S、ψ(t) = T（s²t ↦ S²T 是 2 阶，即双对换的像）。
--   特征标：χ(s) = tr S = φ̄、χ(s²) = tr A = φ（两个 5-共轭类）。
/- ======================================================================== -/

/-- √5 的平方 = 5（ℂ 版本，供矩阵计算）。 -/
lemma sqrt5_sq : ((Real.sqrt 5 : ℂ) ^ 2) = 5 := by
  have h : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  exact_mod_cast h

/-- √5 的立方 = 5√5（ℂ 版本）。 -/
lemma sqrt5_cube : ((Real.sqrt 5 : ℂ) ^ 3) = 5 * (Real.sqrt 5 : ℂ) := by
  change (Real.sqrt 5 : ℂ) ^ (2 + 1) = 5 * (Real.sqrt 5 : ℂ)
  rw [pow_succ, sqrt5_sq]

/-- √5 的四次方 = 25（ℂ 版本）。 -/
lemma sqrt5_four : ((Real.sqrt 5 : ℂ) ^ 4) = 25 := by
  change (Real.sqrt 5 : ℂ) ^ (2 + 2) = 25
  rw [pow_add]
  rw [sqrt5_sq]
  norm_num

/-- √5 的五次方 = 25√5（ℂ 版本）。 -/
lemma sqrt5_five : ((Real.sqrt 5 : ℂ) ^ 5) = 25 * (Real.sqrt 5 : ℂ) := by
  change (Real.sqrt 5 : ℂ) ^ (4 + 1) = 25 * (Real.sqrt 5 : ℂ)
  rw [pow_succ, sqrt5_four]

/-- c = cos(2π/5) = (√5-1)/4 ∈ Q(√5)。 -/
noncomputable def c5 : ℂ := ((Real.sqrt 5 : ℂ) - 1) / 4

/-- g = φ/2 = (1+√5)/4 ∈ Q(√5)。 -/
noncomputable def g5 : ℂ := (1 + (Real.sqrt 5 : ℂ)) / 4

/-- S = ψ(s)：A³ 的干净形式，5 阶，迹 = (1-√5)/2。 -/
noncomputable def icosahedralS : Matrix (Fin 3) (Fin 3) ℂ :=
  !![ -g5, (1 : ℂ) / 2, -c5; -(1 : ℂ) / 2, -c5, g5; c5, g5, (1 : ℂ) / 2]

/-- T = ψ(t)：循环置换矩阵 [[0,0,1],[1,0,0],[0,1,0]]，3 阶，迹 0。 -/
noncomputable def icosahedralT : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- S⁵ = I。 -/
lemma icosahedralS_pow_five : icosahedralS ^ 5 = 1 := by
  change icosahedralS ^ (4 + 1) = 1
  rw [pow_succ]
  change icosahedralS ^ (3 + 1) * icosahedralS = 1
  rw [pow_succ]
  change icosahedralS ^ (2 + 1) * icosahedralS * icosahedralS = 1
  rw [pow_succ]
  change icosahedralS ^ (1 + 1) * icosahedralS * icosahedralS * icosahedralS = 1
  rw [pow_succ]
  rw [pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc, icosahedralS, c5, g5] <;> ring_nf <;> norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four, sqrt5_five] <;> ring_nf <;> norm_num

/-- T³ = I。 -/
lemma icosahedralT_pow_three : icosahedralT ^ 3 = 1 := by
  change icosahedralT ^ (2 + 1) = 1
  rw [pow_succ]
  change icosahedralT ^ (1 + 1) * icosahedralT = 1
  rw [pow_succ]
  rw [pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc, icosahedralT] <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc] <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc] <;> norm_num

/-- (S²T)² = I。 -/
lemma icosahedralS2T_sq : (icosahedralS ^ 2 * icosahedralT) ^ 2 = 1 := by
  change (icosahedralS ^ (1 + 1) * icosahedralT) ^ (1 + 1) = 1
  rw [pow_succ]
  rw [pow_one]
  rw [pow_succ]
  rw [pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc, icosahedralS, icosahedralT, c5, g5] <;> ring_nf <;> norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four, sqrt5_five] <;> ring_nf <;> norm_num

/-- mulVecLin 保幂：(M^n).mulVecLin = M.mulVecLin^n。 -/
lemma mulVecLin_pow (M : Matrix (Fin 3) (Fin 3) ℂ) (n : ℕ) :
    (M ^ n).mulVecLin = M.mulVecLin ^ n := by
  induction n with
  | zero => simp [Matrix.mulVecLin_one]; rfl
  | succ n ih =>
      rw [pow_succ, Matrix.mulVecLin_mul, ih]
      rfl

/-- S 的逆 = S⁴（S⁵ = 1）。 -/
noncomputable def unitS : (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  ⟨icosahedralS, icosahedralS ^ 4,
    by rw [← pow_succ', icosahedralS_pow_five],
    by rw [← pow_succ, icosahedralS_pow_five]⟩

/-- T 的逆 = T²（T³ = 1）。 -/
noncomputable def unitT : (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  ⟨icosahedralT, icosahedralT ^ 2,
    by rw [← pow_succ', icosahedralT_pow_three],
    by rw [← pow_succ, icosahedralT_pow_three]⟩

/-- ψ : P →* GL₃ ℂ（以矩阵 Units 表示）：s ↦ S、t ↦ T。 -/
noncomputable def icosahedralPsi : P →* (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  PresentedGroup.toGroup (f := fun i : Fin 2 => if i = 0 then unitS else unitT) (by
    intro r hr
    simp [rels] at hr
    rcases hr with rfl | rfl | rfl
    · simp
      ext
      simp [unitS, Units.val_pow_eq_pow_val, Units.val_one, icosahedralS_pow_five]
    · simp
      ext
      simp [unitT, Units.val_pow_eq_pow_val, Units.val_one, icosahedralT_pow_three]
    · simp
      ext
      simp [unitS, unitT, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one,
        icosahedralS2T_sq]
  )

/- ======================================================================== -/
-- #3c：呈现完整性 |P| = 60（Todd-Coxeter 陪集枚举，分步击破）
--
-- 第一步：P 中生成元 a = of 0、b = of 1 的阶（陪集枚举的前提）。
/- ======================================================================== -/

/-- P 中 a = of 0 的阶 = 5。 -/
lemma orderOf_a : orderOf (PresentedGroup.of (rels := rels) (0 : Fin 2)) = 5 := by
  apply orderOf_eq_prime
  · have hmem : (FreeGroup.of (0 : Fin 2)) ^ 5 ∈ rels := by
      simp [rels]
    simpa [PresentedGroup.of] using PresentedGroup.one_of_mem (rels := rels) hmem
  · intro h
    have hφ : sG = (1 : G) := by
      have hval : φ (PresentedGroup.of (rels := rels) (0 : Fin 2)) = sG := by
        simp [φ, PresentedGroup.toGroup.of]
      have h1 : φ (PresentedGroup.of (rels := rels) (0 : Fin 2)) = (1 : G) := by
        simpa using congrArg φ h
      rwa [hval] at h1
    have hs : (s : Equiv.Perm (Fin 5)) = 1 := congrArg Subtype.val hφ
    have hs0 : s 0 = 0 := by simpa using congrArg (fun e : Equiv.Perm (Fin 5) => e 0) hs
    have hs0' : s 0 = 1 := by decide
    rw [hs0] at hs0'
    norm_num at hs0'

/-- P 中 b = of 1 的阶 = 3。 -/
lemma orderOf_b : orderOf (PresentedGroup.of (rels := rels) (1 : Fin 2)) = 3 := by
  apply orderOf_eq_prime
  · have hmem : (FreeGroup.of (1 : Fin 2)) ^ 3 ∈ rels := by
      simp [rels]
    simpa [PresentedGroup.of] using PresentedGroup.one_of_mem (rels := rels) hmem
  · intro h
    have hφ : tG = (1 : G) := by
      have hval : φ (PresentedGroup.of (rels := rels) (1 : Fin 2)) = tG := by
        simp [φ, PresentedGroup.toGroup.of]
      have h1 : φ (PresentedGroup.of (rels := rels) (1 : Fin 2)) = (1 : G) := by
        simpa using congrArg φ h
      rwa [hval] at h1
    apply t_is_three_cycle.ne_one
    exact congrArg Subtype.val hφ

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- 关系元 a²·b = of 0² · of 1 的阶 = 2。 -/
lemma orderOf_a2b :
    orderOf ((PresentedGroup.of (rels := rels) (0 : Fin 2)) ^ 2 * PresentedGroup.of (rels := rels) (1 : Fin 2)) = 2 := by
  apply orderOf_eq_prime
  · have hmem : ((FreeGroup.of (0 : Fin 2)) ^ 2 * (FreeGroup.of (1 : Fin 2))) ^ 2 ∈ rels := by
      simp [rels]
    simpa [PresentedGroup.of] using PresentedGroup.one_of_mem (rels := rels) hmem
  · intro h
    have hφ : sG ^ 2 * tG = (1 : G) := by
      have hval : φ ((PresentedGroup.of (rels := rels) (0 : Fin 2)) ^ 2 * PresentedGroup.of (rels := rels) (1 : Fin 2)) = sG ^ 2 * tG := by
        simp [φ, PresentedGroup.toGroup.of, map_mul, map_pow]
      have h1 : φ ((PresentedGroup.of (rels := rels) (0 : Fin 2)) ^ 2 * PresentedGroup.of (rels := rels) (1 : Fin 2)) = (1 : G) := by
        simpa using congrArg φ h
      rwa [hval] at h1
    have hne : sG ^ 2 * tG ≠ (1 : G) := by decide
    exact hne hφ

-- #3c 主体：Todd-Coxeter 陪集枚举证 |P| = 60
-- H = ⟨a⟩（5 阶），P/H 的 12 个左陪集。作用表与代表字已由 Python 数值验证（A5CharQ5/tc_check.py）。
/- ======================================================================== -/

/-- 呈现 P 的生成元 a = of 0。 -/
abbrev pA : P := PresentedGroup.of (rels := rels) (0 : Fin 2)

/-- 呈现 P 的生成元 b = of 1。 -/
abbrev pB : P := PresentedGroup.of (rels := rels) (1 : Fin 2)

/-- 陪集代表 c : Fin 12 → P。最短生成元字（tc_check.py 输出）：
0:1, 1:b, 2:ab, 3:b², 4:ab², 5:bab, 6:a²b², 7:abab, 8:b·ab², 9:b²·ab, 10:a·b·ab², 11:b·a·b·ab²。 -/
def cosetRep : Fin 12 → P :=
  ![1, pB, pA * pB, pB * pB, pA * pB * pB, pB * pA * pB, pA * pA * pB * pB,
    pA * pB * pA * pB, pB * pA * pB * pB, pB * pB * pA * pB,
    pA * pB * pA * pB * pB, pB * pA * pB * pA * pB * pB]

/-- 关系元 a⁵ = 1。 -/
lemma pA_pow_five : pA ^ 5 = 1 := by
  rw [← orderOf_a]
  exact pow_orderOf_eq_one pA

/-- 关系元 b³ = 1。 -/
lemma pB_pow_three : pB ^ 3 = 1 := by
  rw [← orderOf_b]
  exact pow_orderOf_eq_one pB

/-- 关系元 (a²b)² = 1。 -/
lemma pA2B_pow_two : (pA ^ 2 * pB) ^ 2 = 1 := by
  have hmem : ((FreeGroup.of (0 : Fin 2)) ^ 2 * (FreeGroup.of (1 : Fin 2))) ^ 2 ∈ rels := by
    simp [rels]
  simpa [pA, pB, PresentedGroup.of] using PresentedGroup.one_of_mem (rels := rels) hmem

/-- 样板作用引理：a·c0 = c0·a¹（表 0: a→0）。 -/
lemma coset_a_0 : ∃ k : Fin 5, pA * cosetRep 0 = cosetRep 0 * pA ^ k.val := by
  use (1 : Fin 5)
  simp [cosetRep]

/-- 样板作用引理：b·c3 = c0·a⁰（b³ = 1，表 3: b→0）。 -/
lemma coset_b_3 : ∃ k : Fin 5, pB * cosetRep 3 = cosetRep 0 * pA ^ k.val := by
  use (0 : Fin 5)
  simp [cosetRep]
  rw [← mul_assoc]
  change pB ^ 3 = 1
  exact pB_pow_three

/- ========================================================================
#3c 收尾：Todd-Coxeter 陪集枚举 → |P| = 60

数学（tc_check.py 数值确认）：
  12 个陪集代表 cᵢ（最短字），H = ⟨a⟩（5 阶）。
  作用表 a·cᵢ = c_{aT i}·a^{k}、b·cᵢ = c_{bT i}·a^{k}（24 条）。
  指数辅助：a^m·a^n = a^{(m+n) mod 5}；生成元逆 = 正幂（a⁻¹ = a⁴、b⁻¹ = b²）。
  交换引理（自 (a²b)² = 1）：b·a² = a³·b²、a²·b = b²·a³。
  标准形 S := {cᵢ·aᵏ}：
    · 1, pA, pB ∈ S；S 对左乘 pA、pB 封闭（24 条作用引理）；
    · 故 Submonoid.closure {pA,pB} ⊆ S；
    · P ⊆ Submonoid.closure {pA,pB}（自由群归纳：生成元逆 = 正幂）；
    · S = univ → 单射 P → Fin 12 × Fin 5 → |P| ≤ 60；
    · φ 满射 → 60 ≤ |P| → |P| = 60。
=======================================================================-/

-- 作用目标映射（TC 表 a 列、b 列）
def aTarget : Fin 12 → Fin 12 :=
  ![0, 2, 3, 4, 6, 7, 1, 8, 10, 5, 9, 11]

def bTarget : Fin 12 → Fin 12 :=
  ![1, 3, 5, 0, 8, 9, 4, 10, 6, 2, 11, 7]

-- 指数辅助：a^n = a^(n mod 5)
lemma pA_pow_mod (n : ℕ) : pA ^ n = pA ^ (n % 5) := by
  rw [← Nat.mod_add_div n 5, pow_add, pow_mul, pA_pow_five]
  simp

-- Fin 5 指数加法：a^m·a^k = a^(m+k)
lemma pA_pow_add_fin (m k : Fin 5) :
    pA ^ m.val * pA ^ k.val = pA ^ (m + k).val := by
  rw [← pow_add]
  nth_rewrite 1 [pA_pow_mod]
  rfl

-- 生成元逆 = 正幂：a⁻¹ = a⁴、b⁻¹ = b²
lemma pA_inv : pA⁻¹ = pA ^ 4 := by
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [← pow_succ']
  exact pA_pow_five

lemma pB_inv : pB⁻¹ = pB ^ 2 := by
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [← pow_succ']
  exact pB_pow_three

-- 交换引理（自 (a²b)² = 1）：b·a² = a³·b²
lemma b_a2_comm : pB * pA ^ 2 = pA ^ 3 * pB ^ 2 := by
  have h1 : pA ^ 2 * pB * pA ^ 2 * pB = 1 := by
    calc pA ^ 2 * pB * pA ^ 2 * pB
        = pA ^ 2 * pB * (pA ^ 2 * pB) := by rw [mul_assoc]
        _ = (pA ^ 2 * pB) ^ 2 := by rw [← pow_two]
        _ = 1 := pA2B_pow_two
  have ha3 : (pA ^ 2)⁻¹ = pA ^ 3 := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_add]
    exact pA_pow_five
  have hb2 : pB⁻¹ = pB ^ 2 := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ']
    exact pB_pow_three
  have h2 : pA ^ 2 * pB * pA ^ 2 = pB⁻¹ := by
    calc pA ^ 2 * pB * pA ^ 2
        = (pA ^ 2 * pB * pA ^ 2 * pB) * pB⁻¹ := by rw [mul_inv_cancel_right]
        _ = 1 * pB⁻¹ := by rw [h1]
        _ = pB⁻¹ := by simp
  calc pB * pA ^ 2
      = 1 * (pB * pA ^ 2) := by rw [one_mul]
      _ = ((pA ^ 2)⁻¹ * pA ^ 2) * (pB * pA ^ 2) := by simp
      _ = (pA ^ 2)⁻¹ * (pA ^ 2 * pB * pA ^ 2) := by rw [mul_assoc, mul_assoc]
      _ = (pA ^ 2)⁻¹ * pB⁻¹ := by rw [h2]
      _ = pA ^ 3 * pB ^ 2 := by rw [ha3, hb2]

-- 共轭形式：a²·b = b²·a³
lemma a2_b_comm : pA ^ 2 * pB = pB ^ 2 * pA ^ 3 := by
  have h5 : pA ^ 2 * pA ^ 3 = 1 := by
    rw [← pow_add]
    norm_num
    exact pA_pow_five
  have hmid : pA ^ 2 * (pB * pA ^ 2) = pB ^ 2 := by
    calc pA ^ 2 * (pB * pA ^ 2)
        = pA ^ 2 * (pA ^ 3 * pB ^ 2) := by rw [b_a2_comm]
        _ = pA ^ 2 * pA ^ 3 * pB ^ 2 := by rw [← mul_assoc]
        _ = 1 * pB ^ 2 := by rw [h5]
        _ = pB ^ 2 := by simp
  have hL : pA ^ 2 * (pB * pA ^ 2) * pA ^ 3 = pA ^ 2 * pB := by
    calc pA ^ 2 * (pB * pA ^ 2) * pA ^ 3
        = pA ^ 2 * ((pB * pA ^ 2) * pA ^ 3) := by rw [mul_assoc]
        _ = pA ^ 2 * (pB * (pA ^ 2 * pA ^ 3)) := by rw [mul_assoc]
        _ = pA ^ 2 * (pB * 1) := by rw [h5]
        _ = pA ^ 2 * pB := by simp
  calc pA ^ 2 * pB
      = pA ^ 2 * (pB * pA ^ 2) * pA ^ 3 := hL.symm
      _ = pB ^ 2 * pA ^ 3 := by rw [hmid]

-- 自 (a²b)² = 1 的导出引理（tc_reduce.py BFS 验证）：
--   C: a²·b·a² = b²、D: b·a²·b = a³、F: a·b·a = a⁴·b²·a⁴、G: b²·a²·b² = b·a³·b
lemma pB_pow_four : pB ^ 4 = pB := by
  calc pB ^ 4 = pB ^ 3 * pB := by rw [← pow_succ]
      _ = 1 * pB := by rw [pB_pow_three]
      _ = pB := by simp

lemma a2_b_a2_eq_b2 : pA ^ 2 * pB * pA ^ 2 = pB ^ 2 := by
  have h1 : pA ^ 2 * pB * pA ^ 2 * pB = 1 := by
    calc pA ^ 2 * pB * pA ^ 2 * pB
        = pA ^ 2 * pB * (pA ^ 2 * pB) := by rw [mul_assoc]
        _ = (pA ^ 2 * pB) ^ 2 := by rw [← pow_two]
        _ = 1 := pA2B_pow_two
  calc pA ^ 2 * pB * pA ^ 2
      = (pA ^ 2 * pB * pA ^ 2 * pB) * pB⁻¹ := by rw [mul_inv_cancel_right]
      _ = 1 * pB⁻¹ := by rw [h1]
      _ = pB⁻¹ := by simp
      _ = pB ^ 2 := pB_inv

lemma b_a2_b_eq_a3 : pB * pA ^ 2 * pB = pA ^ 3 := by
  have h1' : pA ^ 2 * (pB * pA ^ 2 * pB) = 1 := by
    calc pA ^ 2 * (pB * pA ^ 2 * pB)
        = pA ^ 2 * pB * pA ^ 2 * pB := by rw [← mul_assoc, ← mul_assoc]
        _ = pA ^ 2 * pB * (pA ^ 2 * pB) := by rw [mul_assoc]
        _ = (pA ^ 2 * pB) ^ 2 := by rw [← pow_two]
        _ = 1 := pA2B_pow_two
  have ha3 : (pA ^ 2)⁻¹ = pA ^ 3 := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_add]
    exact pA_pow_five
  calc pB * pA ^ 2 * pB
      = (pA ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1'
      _ = pA ^ 3 := ha3

lemma a_b_a_eq_a4_b2_a4 : pA * pB * pA = pA ^ 4 * pB ^ 2 * pA ^ 4 := by
  have hL : pA * (pB * pA ^ 2) * pA ^ 4 = pA * pB * pA := by
    calc pA * (pB * pA ^ 2) * pA ^ 4
        = pA * pB * pA ^ 2 * pA ^ 4 := by rw [← mul_assoc]
        _ = pA * pB * (pA ^ 2 * pA ^ 4) := by rw [← mul_assoc]
        _ = pA * pB * pA := by
          rw [show pA ^ 2 * pA ^ 4 = pA by
            rw [← pow_add, pA_pow_mod]
            norm_num]
  have hR : pA * (pA ^ 3 * pB ^ 2) * pA ^ 4 = pA ^ 4 * pB ^ 2 * pA ^ 4 := by
    calc pA * (pA ^ 3 * pB ^ 2) * pA ^ 4
        = pA * pA ^ 3 * pB ^ 2 * pA ^ 4 := by rw [← mul_assoc]
        _ = pA ^ 4 * pB ^ 2 * pA ^ 4 := by
          rw [show pA * pA ^ 3 = pA ^ 4 by rw [← pow_succ']]
  calc pA * pB * pA
      = pA * (pB * pA ^ 2) * pA ^ 4 := hL.symm
      _ = pA * (pA ^ 3 * pB ^ 2) * pA ^ 4 := by rw [b_a2_comm]
      _ = pA ^ 4 * pB ^ 2 * pA ^ 4 := hR

lemma b2_a2_b2_eq_b_a3_b : pB ^ 2 * pA ^ 2 * pB ^ 2 = pB * pA ^ 3 * pB := by
  calc pB ^ 2 * pA ^ 2 * pB ^ 2
      = ((pB * pB) * pA ^ 2) * (pB * pB) := by rw [pow_two, pow_two]
      _ = ((pB * pB) * (pA ^ 2 * pB)) * pB := by
          rw [← mul_assoc]
          nth_rewrite 2 [mul_assoc]
          rfl
      _ = ((pB * pB) * (pB ^ 2 * pA ^ 3)) * pB := by rw [a2_b_comm]
      _ = (((pB * pB) * pB ^ 2) * pA ^ 3) * pB := by rw [← mul_assoc]
      _ = ((pB ^ 2 * pB ^ 2) * pA ^ 3) * pB := by rw [← pow_two]
      _ = (pB ^ 4 * pA ^ 3) * pB := by rw [← pow_add]
      _ = (pB * pA ^ 3) * pB := by rw [pB_pow_four]

-- 导出引理（tc_chain2.py 数值验证）：hba：b²·a = a²·b·a³
lemma hba : pB ^ 2 * pA = pA ^ 2 * pB * pA ^ 3 := by
  calc pB ^ 2 * pA
      = pA ^ 2 * pB * pA ^ 2 * pA := by rw [← a2_b_a2_eq_b2]
      _ = (pA ^ 2 * pB) * (pA ^ 2 * pA) := by rw [mul_assoc]
      _ = pA ^ 2 * pB * pA ^ 3 := by rw [← pow_succ]

-- 导出引理（tc_chain2.py 数值验证）：hbab4：b·a⁴·b = a³·b·a³
lemma hbab4 : pB * pA ^ 4 * pB = pA ^ 3 * pB * pA ^ 3 := by
  calc pB * pA ^ 4 * pB
      = pB * (pA ^ 2 * pA ^ 2) * pB := by
        rw [show pA ^ 4 = pA ^ 2 * pA ^ 2 by rw [← pow_add]]
      _ = pB * pA ^ 2 * pA ^ 2 * pB := by rw [← mul_assoc]
      _ = (pB * pA ^ 2) * (pA ^ 2 * pB) := by rw [mul_assoc]
      _ = (pA ^ 3 * pB ^ 2) * (pB ^ 2 * pA ^ 3) := by rw [b_a2_comm, a2_b_comm]
      _ = pA ^ 3 * (pB ^ 2 * (pB ^ 2 * pA ^ 3)) := by rw [mul_assoc]
      _ = pA ^ 3 * ((pB ^ 2 * pB ^ 2) * pA ^ 3) := by
        rw [show pB ^ 2 * (pB ^ 2 * pA ^ 3) = (pB ^ 2 * pB ^ 2) * pA ^ 3 by rw [← mul_assoc]]
      _ = pA ^ 3 * (pB ^ 4 * pA ^ 3) := by
        rw [show pB ^ 2 * pB ^ 2 = pB ^ 4 by rw [← pow_add]]
      _ = pA ^ 3 * (pB * pA ^ 3) := by rw [pB_pow_four]
      _ = pA ^ 3 * pB * pA ^ 3 := by rw [← mul_assoc]

-- 24 条作用引理（TC 表数值；简单条直接 simp 闭合）
lemma coset_a_1 : ∃ k : Fin 5, pA * cosetRep 1 = cosetRep 2 * pA ^ k.val := by
  use (0 : Fin 5)
  simp [cosetRep]

lemma coset_a_2 : ∃ k : Fin 5, pA * cosetRep 2 = cosetRep 3 * pA ^ k.val := by
  use (3 : Fin 5)
  change pA * (pA * pB) = pB * pB * pA ^ 3
  calc pA * (pA * pB)
      = pA * pA * pB := by rw [← mul_assoc]
      _ = pA ^ 2 * pB := by rw [← pow_two]
      _ = pB ^ 2 * pA ^ 3 := a2_b_comm

lemma coset_a_3 : ∃ k : Fin 5, pA * cosetRep 3 = cosetRep 4 * pA ^ k.val := by
  use (0 : Fin 5)
  change pA * (pB * pB) = (pA * pB * pB) * 1
  rw [← mul_assoc]
  simp

lemma coset_a_4 : ∃ k : Fin 5, pA * cosetRep 4 = cosetRep 6 * pA ^ k.val := by
  use (0 : Fin 5)
  change pA * (pA * pB * pB) = (pA * pA * pB * pB) * 1
  rw [← mul_assoc, ← mul_assoc]
  simp

lemma coset_a_5 : ∃ k : Fin 5, pA * cosetRep 5 = cosetRep 7 * pA ^ k.val := by
  use (0 : Fin 5)
  change pA * (pB * pA * pB) = (pA * pB * pA * pB) * 1
  rw [← mul_assoc, ← mul_assoc]
  simp

lemma coset_a_6 : ∃ k : Fin 5, pA * cosetRep 6 = cosetRep 1 * pA ^ k.val := by
  use (2 : Fin 5)
  change pA * (pA * pA * pB * pB) = pB * pA ^ 2
  calc pA * (pA * pA * pB * pB)
      = pA * pA * pA * pB * pB := by rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
      _ = pA ^ 3 * pB * pB := by rw [← pow_three']
      _ = pA ^ 3 * pB ^ 2 := by rw [mul_assoc, ← pow_two]
      _ = pB * pA ^ 2 := b_a2_comm.symm

lemma coset_a_8 : ∃ k : Fin 5, pA * cosetRep 8 = cosetRep 10 * pA ^ k.val := by
  use (0 : Fin 5)
  change pA * (pB * pA * pB * pB) = (pA * pB * pA * pB * pB) * 1
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  simp

lemma coset_b_0 : ∃ k : Fin 5, pB * cosetRep 0 = cosetRep 1 * pA ^ k.val := by
  use (0 : Fin 5)
  simp [cosetRep]

lemma coset_b_1 : ∃ k : Fin 5, pB * cosetRep 1 = cosetRep 3 * pA ^ k.val := by
  use (0 : Fin 5)
  simp [cosetRep]

lemma coset_b_2 : ∃ k : Fin 5, pB * cosetRep 2 = cosetRep 5 * pA ^ k.val := by
  use (0 : Fin 5)
  change pB * (pA * pB) = (pB * pA * pB) * 1
  rw [← mul_assoc]
  simp

lemma coset_b_4 : ∃ k : Fin 5, pB * cosetRep 4 = cosetRep 8 * pA ^ k.val := by
  use (0 : Fin 5)
  change pB * (pA * pB * pB) = (pB * pA * pB * pB) * 1
  rw [← mul_assoc, ← mul_assoc]
  simp

lemma coset_b_5 : ∃ k : Fin 5, pB * cosetRep 5 = cosetRep 9 * pA ^ k.val := by
  use (0 : Fin 5)
  change pB * (pB * pA * pB) = (pB * pB * pA * pB) * 1
  rw [← mul_assoc, ← mul_assoc]
  simp

lemma coset_b_9 : ∃ k : Fin 5, pB * cosetRep 9 = cosetRep 2 * pA ^ k.val := by
  use (0 : Fin 5)
  change pB * (pB * pB * pA * pB) = (pA * pB) * 1
  calc pB * (pB * pB * pA * pB)
      = pB * pB * pB * pA * pB := by rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
      _ = pB ^ 3 * pA * pB := by rw [← pow_three']
      _ = 1 * pA * pB := by rw [pB_pow_three]
      _ = pA * pB := by simp
      _ = (pA * pB) * 1 := by rw [mul_one]

lemma coset_b_10 : ∃ k : Fin 5, pB * cosetRep 10 = cosetRep 11 * pA ^ k.val := by
  use (0 : Fin 5)
  change pB * (pA * pB * pA * pB * pB) = (pB * pA * pB * pA * pB * pB) * 1
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  simp

-- 8 条复杂作用引理（tc_reduce.py BFS 重写路径；每步 = 交换引理 + 结合/幂处理）
lemma coset_a_7 : ∃ k : Fin 5, pA * cosetRep 7 = cosetRep 8 * pA ^ k.val := by
  use (1 : Fin 5)
  change pA * (pA * pB * pA * pB) = pB * pA * pB * pB * pA
  calc pA * (pA * pB * pA * pB)
      = pA * pA * pB * pA * pB := by rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  _ = pA ^ 2 * pB * pA * pB := by rw [← pow_two]
  _ = pB ^ 2 * pA ^ 3 * pA * pB := by rw [a2_b_comm]
  _ = pB ^ 2 * pA ^ 4 * pB := by
    nth_rewrite 2 [mul_assoc]
    rw [← pow_succ]
  _ = pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 3 := by
    rw [show pA ^ 4 = pA ^ 2 * pA ^ 2 by
      calc pA ^ 4 = pA ^ (2 + 2) := by norm_num
          _ = pA ^ 2 * pA ^ 2 := by rw [pow_add]]
    rw [← mul_assoc, mul_assoc, a2_b_comm, ← mul_assoc]
  _ = pB * pA ^ 3 * pB * pA ^ 3 := by
    rw [b2_a2_b2_eq_b_a3_b]
  _ = pB * pA * pB ^ 2 * pA := by
    change pB * (pA * pA ^ 2) * pB * pA ^ 3 = pB * pA * pB ^ 2 * pA
    rw [← mul_assoc]
    nth_rewrite 2 [mul_assoc]
    rw [a2_b_comm]
    rw [← mul_assoc]
    rw [mul_assoc]
    rw [← pow_add]
    rw [show pA ^ 6 = pA by
      calc pA ^ 6 = pA ^ (5 + 1) := by rw [show (6 : ℕ) = 5 + 1 by norm_num]
          _ = pA * pA ^ 5 := by rw [pow_succ']
          _ = pA * 1 := by rw [pA_pow_five]
          _ = pA := by simp]

lemma coset_a_9 : ∃ k : Fin 5, pA * cosetRep 9 = cosetRep 5 * pA ^ k.val := by
  use (2 : Fin 5)
  change pA * (pB * pB * pA * pB) = pB * pA * pB * pA * pA
  calc pA * (pB * pB * pA * pB)
      = pA * pB * pB * pA * pB := by rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  _ = pA * (pB * pB) * pA * pB := by rw [← mul_assoc]
  _ = pA * pB ^ 2 * pA * pB := by rw [← pow_two]
  _ = pA * (pA ^ 2 * pB * pA ^ 2) * pA * pB := by rw [← a2_b_a2_eq_b2]
  _ = pA * pA ^ 2 * pB * pA ^ 2 * pA * pB := by rw [← mul_assoc, ← mul_assoc]
  _ = pA ^ 3 * pB * pA ^ 3 * pB := by
    rw [← pow_succ']
    norm_num
    rw [mul_assoc]
    rw [← pow_succ]
  _ = pB * pA ^ 2 * pB * pB * pA ^ 3 * pB := by
    rw [show (pA ^ 3 * pB) * pA ^ 3 = pB * pA ^ 2 * pB * pB * pA ^ 3 by
      rw [show pA ^ 3 * pB = pB * pA ^ 2 * pB * pB by rw [← b_a2_b_eq_a3]]]
  _ = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB := by
    rw [show ((pB * pA ^ 2) * pB) * pB = pB * pA ^ 2 * pB ^ 2 by
      rw [mul_assoc]
      rw [← pow_two]]
  _ = pB * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pB := by
    rw [show ((pB * pA ^ 2) * pB ^ 2) * pA ^ 3 = pB * pA ^ 2 * (pB ^ 2 * pA ^ 3) by
      rw [mul_assoc]]
  _ = pB * pA ^ 2 * (pA ^ 2 * pB) * pB := by
    rw [show (pB * pA ^ 2) * (pB ^ 2 * pA ^ 3) = pB * pA ^ 2 * (pA ^ 2 * pB) by
      rw [← a2_b_comm]]
  _ = pB * pA ^ 4 * pB ^ 2 := by
    rw [← mul_assoc]
    rw [show ((pB * pA ^ 2) * pA ^ 2) * pB = pB * pA ^ 4 * pB by
      calc ((pB * pA ^ 2) * pA ^ 2) * pB
          = pB * (pA ^ 2 * pA ^ 2) * pB := by
              rw [show ((pB * pA ^ 2) * pA ^ 2) = pB * (pA ^ 2 * pA ^ 2) by
                rw [mul_assoc]]
          _ = pB * pA ^ 4 * pB := by
              rw [← pow_add]]
    rw [mul_assoc]
    rw [← pow_two]
  _ = pB * pA * (pB * pA ^ 2) := by
    rw [show pA ^ 4 = pA * pA ^ 3 by rw [← pow_succ']]
    rw [← mul_assoc]
    rw [mul_assoc]
    rw [← b_a2_comm]

lemma coset_a_10 : ∃ k : Fin 5, pA * cosetRep 10 = cosetRep 9 * pA ^ k.val := by
  use (2 : Fin 5)
  change pA * (pA * pB * pA * pB * pB) = pB * pB * pA * pB * pA * pA
  calc pA * (pA * pB * pA * pB * pB)
      = pA * pA * pB * pA * pB * pB := by
        rw [← mul_assoc]
        rw [← mul_assoc]
        rw [← mul_assoc]
        rw [← mul_assoc]
  _ = pA ^ 2 * pB * pA * pB * pB := by rw [← pow_two]
  _ = pB ^ 2 * pA ^ 3 * pA * pB * pB := by rw [a2_b_comm]
  _ = pB ^ 2 * pA ^ 4 * pB * pB := by
    nth_rewrite 3 [mul_assoc]
    rw [← pow_succ]
  _ = pB ^ 2 * pA ^ 4 * pB ^ 2 := by
    rw [mul_assoc]
    rw [← pow_two]
  _ = pB ^ 2 * pA * (pB * pA ^ 2) := by
    rw [show pA ^ 4 = pA * pA ^ 3 by rw [← pow_succ']]
    rw [← mul_assoc]
    rw [mul_assoc]
    rw [← b_a2_comm]

lemma coset_a_11 : ∃ k : Fin 5, pA * cosetRep 11 = cosetRep 11 * pA ^ k.val := by
  use (4 : Fin 5)
  change pA * (pB * pA * pB * pA * pB * pB) = pB * pA * pB * pA * pB * pB * pA * pA * pA * pA
  calc pA * (pB * pA * pB * pA * pB * pB)
      = pA * pB * pA * pB * pA * pB * pB := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  -- Ci：b² → a²·b·a²（位置 5）
  _ = pA * pB * pA * pB * pA ^ 3 * pB * pA ^ 2 := by
    calc pA * pB * pA * pB * pA * pB * pB
        = pA * pB * pA * pB * pA * (pB * pB) := by
            nth_rewrite 4 [mul_assoc]
            rfl
        _ = pA * pB * pA * pB * pA * pB ^ 2 := by rw [← pow_two]
        _ = pA * pB * pA * pB * pA * (pA ^ 2 * pB * pA ^ 2) := by rw [← a2_b_a2_eq_b2]
        _ = (pA * pB * pA * pB * pA * (pA ^ 2 * pB)) * pA ^ 2 := by rw [← mul_assoc]
        _ = (pA * pB * pA * pB * pA * pA ^ 2) * pB * pA ^ 2 := by rw [← mul_assoc]
        _ = pA * pB * pA * pB * (pA * pA ^ 2) * pB * pA ^ 2 := by
            nth_rewrite 3 [mul_assoc]
            rfl
        _ = pA * pB * pA * pB * pA ^ 3 * pB * pA ^ 2 := by
            rw [← pow_succ']
  -- Di：a³ → b·a²·b（位置 4）
  _ = pA * pB * pA * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
    calc pA * pB * pA * pB * pA ^ 3 * pB * pA ^ 2
        = pA * pB * pA * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 2 := by
            rw [show pA ^ 3 = pB * pA ^ 2 * pB by rw [← b_a2_b_eq_a3]]
        _ = (pA * pB * pA * pB * (pB * pA ^ 2)) * pB * pB * pA ^ 2 := by
            rw [← mul_assoc]
        _ = pA * pB * pA * pB * pB * pA ^ 2 * pB * pB * pA ^ 2 := by
            rw [← mul_assoc]
        _ = pA * pB * pA * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
            rw [show pA * pB * pA * pB * pB * pA ^ 2 * pB * pB * pA ^ 2
                = pA * pB * pA * pB * pB * pA ^ 2 * (pB * pB) * pA ^ 2 by group]
            rw [← pow_two]
  -- Ci：b² → a²·b·a²（位置 5）
  _ = pA * pB * pA ^ 3 * pB * pA ^ 4 * pB ^ 2 * pA ^ 2 := by
    calc pA * pB * pA * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 2
        = pA * pB * pA * (pB * pB) * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
            nth_rewrite 3 [mul_assoc]
            rfl
        _ = pA * pB * pA * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
            rw [← pow_two]
        _ = pA * pB * pA * (pA ^ 2 * pB * pA ^ 2) * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
            rw [← a2_b_a2_eq_b2]
        _ = (pA * pB * pA * (pA ^ 2 * pB)) * pA ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
            rw [← mul_assoc]
        _ = (pA * pB * pA * pA ^ 2) * pB * pA ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
            rw [← mul_assoc]
        _ = pA * pB * (pA * pA ^ 2) * pB * pA ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
            nth_rewrite 2 [mul_assoc]
            rfl
        _ = pA * pB * pA ^ 3 * pB * pA ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 2 := by
            rw [← pow_succ']
        _ = pA * pB * pA ^ 3 * pB * (pA ^ 2 * pA ^ 2) * pB ^ 2 * pA ^ 2 := by
            nth_rewrite 4 [mul_assoc]
            rfl
        _ = pA * pB * pA ^ 3 * pB * pA ^ 4 * pB ^ 2 * pA ^ 2 := by
            rw [← pow_add]
  -- Bi：a³·b² → b·a²（位置 5）
  _ = pA * pB * pA ^ 3 * pB * pA * pB * pA ^ 4 := by
    rw [show pA * pB * pA ^ 3 * pB * pA ^ 4 * pB ^ 2 * pA ^ 2
        = pA * pB * pA ^ 3 * pB * pA * (pA ^ 3 * pB ^ 2) * pA ^ 2 by group]
    rw [← b_a2_comm]
    rw [show pA * pB * pA ^ 3 * pB * pA * (pB * pA ^ 2) * pA ^ 2
        = pA * pB * pA ^ 3 * pB * pA * pB * pA ^ 4 by group]
  -- Ci：a³ → b·a²·b（位置 3）
  _ = pA * pB * pB * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4 := by
    rw [← b_a2_b_eq_a3]
    rw [show pA * pB * (pB * pA ^ 2 * pB) * pB * pA * pB * pA ^ 4
        = pA * pB * pB * (pA ^ 2 * pB) * pB * pA * pB * pA ^ 4 by group]
    rw [show pA * pB * pB * (pA ^ 2 * pB) * pB * pA * pB * pA ^ 4
        = pA * pB * pB * pA ^ 2 * (pB * pB) * pA * pB * pA ^ 4 by group]
    rw [← pow_two]
  -- Di：bb → a²·b·a²（位置 1-2）＋幂合并
  _ = pA ^ 3 * pB * pA ^ 4 * pB ^ 2 * pA * pB * pA ^ 4 := by
    rw [show pA * pB * pB * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4
        = pA * (pB * pB) * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4 by group]
    rw [show pA * (pB * pB) * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4
        = pA * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4 by
          rw [← pow_two]]
    nth_rewrite 1 [← a2_b_a2_eq_b2]
    rw [show pA * (pA ^ 2 * pB * pA ^ 2) * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4
        = (pA * pA ^ 2) * pB * (pA ^ 2 * pA ^ 2) * pB ^ 2 * pA * pB * pA ^ 4 by group]
    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- Di：a³·b² → b·a²（位置 5）＋幂拆合
  _ = pA ^ 3 * pB * pA * pB * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite 1 [show pA ^ 4 = pA * pA ^ 3 by rw [pow_succ']]
    rw [show pA ^ 3 * pB * (pA * pA ^ 3) * pB ^ 2 * pA * pB * pA ^ 4
        = pA ^ 3 * pB * pA * (pA ^ 3 * pB ^ 2) * pA * pB * pA ^ 4 by group]
    rw [← b_a2_comm]
    rw [show pA ^ 3 * pB * pA * (pB * pA ^ 2) * pA * pB * pA ^ 4
        = pA ^ 3 * pB * pA * pB * (pA ^ 2 * pA) * pB * pA ^ 4 by group]
    rw [show pA ^ 2 * pA = pA ^ 3 by rw [← pow_succ]]
  -- Bi：a³ → b·a²·b（位置 0）
  _ = pB * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite 1 [← b_a2_b_eq_a3]
    rw [show (pB * pA ^ 2 * pB) * pB * pA * pB * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 2 * (pB * pB) * pA * pB * pA ^ 3 * pB * pA ^ 4 by group]
    rw [← pow_two]
  -- Ci：b² → a²·b·a²（位置 3）＋幂合并
  _ = pB * pA ^ 4 * pB * pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 4 := by
    rw [← a2_b_a2_eq_b2]
    rw [show pB * pA ^ 2 * (pA ^ 2 * pB * pA ^ 2) * pA * pB * pA ^ 3 * pB * pA ^ 4
        = pB * (pA ^ 2 * pA ^ 2) * pB * (pA ^ 2 * pA) * pB * pA ^ 3 * pB * pA ^ 4 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
    rw [show pA ^ 2 * pA = pA ^ 3 by rw [← pow_succ]]
  -- Gi：a³ → b·a²·b（位置 6）＋b·b 合并
  _ = pB * pA ^ 4 * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite 1 [← b_a2_b_eq_a3]
    rw [show pB * pA ^ 4 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 4 * pB * pB * (pA ^ 2 * pB * pB) * pA ^ 3 * pB * pA ^ 4 by group]
    rw [show (pA ^ 2 * pB) * pB = pA ^ 2 * (pB * pB) by rw [← mul_assoc]]
    rw [show pA ^ 2 * (pB * pB) = pA ^ 2 * pB ^ 2 by rw [← pow_two]]
    rw [show pB * pA ^ 4 * pB * pB * (pA ^ 2 * pB ^ 2) * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 4 * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 by group]
  -- Ai：b²·a³ → a²·b（位置 9-13）＋幂合并
  _ = pB * pA ^ 4 * pB ^ 2 * pA ^ 4 * pB ^ 2 * pA ^ 4 := by
    rw [show pB * pA ^ 4 * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 4 * pB * pB * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pB * pA ^ 4 by group]
    rw [← a2_b_comm]
    rw [show pB * pA ^ 4 * pB * pB * pA ^ 2 * (pA ^ 2 * pB) * pB * pA ^ 4
        = pB * pA ^ 4 * (pB * pB) * (pA ^ 2 * pA ^ 2) * (pB * pB) * pA ^ 4 by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- Ai：a⁴·b²·a⁴ → a·b·a（位置 1-10）
  _ = pB * pA * pB * pA * pB ^ 2 * pA ^ 4 := by
    rw [show pB * pA ^ 4 * pB ^ 2 * pA ^ 4 * pB ^ 2 * pA ^ 4
        = pB * (pA ^ 4 * pB ^ 2 * pA ^ 4) * pB ^ 2 * pA ^ 4 by group]
    rw [← a_b_a_eq_a4_b2_a4]
    rw [show pB * (pA * pB * pA) * pB ^ 2 * pA ^ 4
        = pB * pA * pB * pA * pB ^ 2 * pA ^ 4 by group]

lemma coset_b_6 : ∃ k : Fin 5, pB * cosetRep 6 = cosetRep 4 * pA ^ k.val := by
  use (3 : Fin 5)
  change pB * (pA * pA * pB * pB) = pA * pB * pB * pA * pA * pA
  calc pB * (pA * pA * pB * pB)
      = pB * pA * pA * pB * pB := by rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  _ = pB * (pA * pA) * pB * pB := by rw [← mul_assoc]
  _ = pB * pA ^ 2 * pB * pB := by rw [← pow_two]
  _ = pB * (pA ^ 2 * pB) * pB := by rw [← mul_assoc]
  _ = pB * (pB ^ 2 * pA ^ 3) * pB := by rw [a2_b_comm]
  _ = pB * pB ^ 2 * pA ^ 3 * pB := by rw [← mul_assoc]
  _ = pB ^ 3 * pA ^ 3 * pB := by rw [← pow_succ']
  _ = 1 * pA ^ 3 * pB := by rw [pB_pow_three]
  _ = pA ^ 3 * pB := by simp
  _ = pA * pA ^ 2 * pB := by rw [show pA ^ 3 = pA * pA ^ 2 by rw [pow_succ']]
  _ = pA * (pA ^ 2 * pB) := by rw [← mul_assoc]
  _ = pA * (pB ^ 2 * pA ^ 3) := by rw [a2_b_comm]
  _ = pA * pB ^ 2 * pA ^ 3 := by rw [← mul_assoc]

lemma coset_b_7 : ∃ k : Fin 5, pB * cosetRep 7 = cosetRep 10 * pA ^ k.val := by
  use (4 : Fin 5)
  change pB * (pA * pB * pA * pB) = pA * pB * pA * pB * pB * pA * pA * pA * pA
  calc pB * (pA * pB * pA * pB)
      = pB * pA * pB * pA * pB := by rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  -- F：a·b·a → a⁴·b²·a⁴（位置 1，rule4 正向）
  _ = pB * pA ^ 4 * pB ^ 2 * pA ^ 4 * pB := by
    rw [show pB * pA * pB * pA * pB
        = pB * (pA * pB * pA) * pB by group]
    rw [a_b_a_eq_a4_b2_a4]
    rw [show pB * (pA ^ 4 * pB ^ 2 * pA ^ 4) * pB
        = pB * pA ^ 4 * pB ^ 2 * pA ^ 4 * pB by group]
  -- 1：a²·b → b²·a³（位置 3，rule1 正向；跨 a⁴·b² 因子）
  _ = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 2 * pA ^ 2 by rw [← pow_add]]
    nth_rewrite 1 [show pB ^ 2 = pB * pB by rw [pow_two]]
    rw [show pB * (pA ^ 2 * pA ^ 2) * (pB * pB) * pA ^ 4 * pB
        = pB * pA ^ 2 * ((pA ^ 2 * pB) * pB) * pA ^ 4 * pB by group]
    rw [a2_b_comm]
    rw [show pB * pA ^ 2 * ((pB ^ 2 * pA ^ 3) * pB) * pA ^ 4 * pB
        = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB by group]
  -- 2：b·a²·b → a³（位置 0，rule3 正向；跨 b·a²·b² 因子）
  _ = pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 4 * pB := by
    rw [show pB ^ 2 = pB * pB by rw [pow_two]]
    rw [show pB * pA ^ 2 * (pB * pB) * pA ^ 3 * pB * pA ^ 4 * pB
        = (pB * pA ^ 2 * pB) * pB * pA ^ 3 * pB * pA ^ 4 * pB by group]
    rw [b_a2_b_eq_a3]
  -- 3：a²·b·a² → b²（位置 1，rule2 正向；跨 a³·b·a³ 因子）
  _ = pA * pB * pB * pA * pB * pA ^ 4 * pB := by
    rw [show pA ^ 3 = pA * pA ^ 2 by rw [pow_succ']]
    rw [show (pA * pA ^ 2) * pB * (pA * pA ^ 2) * pB * pA ^ 4 * pB
        = pA * (pA ^ 2 * pB * pA ^ 2) * pA * pB * pA ^ 4 * pB by group]
    rw [a2_b_a2_eq_b2]
    rw [show pB ^ 2 = pB * pB by rw [pow_two]]
    rw [show pA * (pB * pB) * pA * pB * pA ^ 4 * pB
        = pA * pB * pB * pA * pB * pA ^ 4 * pB by group]
  -- T1：b·a⁴·b → a³·b·a³（位置 4-9，hbab4 正向）
  _ = pA * pB * pB * pA * (pA ^ 3 * pB * pA ^ 3) := by
    rw [show pA * pB * pB * pA * pB * pA ^ 4 * pB
        = pA * pB * pB * pA * (pB * pA ^ 4 * pB) by group]
    rw [hbab4]
  -- T2：b·a⁴·b → a³·b·a³（位置 2-7，hbab4 正向；先合并 a·a³ → a⁴）
  _ = pA * pB * (pA ^ 3 * pB * pA ^ 3) * pA ^ 3 := by
    rw [show pA * pB * pB * pA * (pA ^ 3 * pB * pA ^ 3)
        = pA * pB * pB * (pA * pA ^ 3) * pB * pA ^ 3 by group]
    rw [show pA * pA ^ 3 = pA ^ 4 by rw [← pow_succ']]
    rw [show pA * pB * pB * pA ^ 4 * pB * pA ^ 3
        = pA * pB * (pB * pA ^ 4 * pB) * pA ^ 3 by group]
    rw [hbab4]
  -- T3：a²·b·a² → b²（位置 3-7，rule2 正向；末尾合并 a·a³ → a⁴）
  _ = pA * pB * pA * pB ^ 2 * pA ^ 4 := by
    rw [show pA * pB * (pA ^ 3 * pB * pA ^ 3) * pA ^ 3
        = pA * pB * pA * (pA ^ 2 * pB * pA ^ 2) * pA * pA ^ 3 by group]
    rw [a2_b_a2_eq_b2]
    rw [show pA * pB * pA * pB ^ 2 * pA * pA ^ 3
        = pA * pB * pA * pB ^ 2 * (pA * pA ^ 3) by group]
    rw [show pA * pA ^ 3 = pA ^ 4 by rw [← pow_succ']]

lemma coset_b_8 : ∃ k : Fin 5, pB * cosetRep 8 = cosetRep 6 * pA ^ k.val := by
  use (2 : Fin 5)
  change pB * (pB * pA * pB * pB) = pA * pA * pB * pB * pA * pA
  calc pB * (pB * pA * pB * pB)
      = pB * pB * pA * pB * pB := by rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  _ = pB ^ 2 * pA * pB * pB := by rw [← pow_two]
  _ = (pA ^ 2 * pB * pA ^ 3) * pB * pB := by rw [hba]
  _ = (pA ^ 2 * pB * pA ^ 3) * (pB * pB) := by rw [mul_assoc]
  _ = (pA ^ 2 * pB * pA ^ 3) * pB ^ 2 := by rw [← pow_two]
  _ = pA ^ 2 * pB * (pA ^ 3 * pB ^ 2) := by rw [mul_assoc]
  _ = pA ^ 2 * pB * (pB * pA ^ 2) := by rw [← b_a2_comm]
  _ = pA ^ 2 * ((pB * pB) * pA ^ 2) := by
    rw [mul_assoc, show pB * (pB * pA ^ 2) = (pB * pB) * pA ^ 2 by rw [← mul_assoc]]
  _ = pA ^ 2 * (pB ^ 2 * pA ^ 2) := by rw [← pow_two]
  _ = pA ^ 2 * pB ^ 2 * pA ^ 2 := by rw [mul_assoc]
  _ = pA * pA * pB * pB * pA * pA := by
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2
        = (pA * pA) * pB ^ 2 * (pA * pA) by
          rw [pow_two]]
    rw [show (pA * pA) * pB ^ 2 * (pA * pA)
        = (pA * pA) * (pB * pB) * (pA * pA) by
          rw [pow_two]]
    rw [show (pA * pA) * (pB * pB) * (pA * pA)
        = pA * pA * pB * pB * pA * pA by group]

lemma coset_b_11 : ∃ k : Fin 5, pB * cosetRep 11 = cosetRep 7 * pA ^ k.val := by
  use (1 : Fin 5)
  change pB * (pB * pA * pB * pA * pB * pB) = pA * pB * pA * pB * pA
  calc pB * (pB * pA * pB * pA * pB * pB)
      = pB * pB * pA * pB * pA * pB * pB := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  -- 1：bb → a²·b·a²（位置 0，rule2 反向；先合并最左 bb）＋幂合并
  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA * pB ^ 2 := by
    rw [show pB * pB * pA * pB * pA * pB * pB
        = pB * pB * pA * pB * pA * (pB * pB) by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
    nth_rewrite 1 [← a2_b_a2_eq_b2]
    rw [show (pA ^ 2 * pB * pA ^ 2) * pA * pB * pA * pB ^ 2
        = pA ^ 2 * pB * (pA ^ 2 * pA) * pB * pA * pB ^ 2 by group]
    rw [show pA ^ 2 * pA = pA ^ 3 by rw [← pow_succ]]
  -- 2：bb → a²·b·a²（位置 8，rule2 反向；尾部 b² 单块）＋幂合并
  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 2 := by
    rw [show pA ^ 2 * pB * pA ^ 3 * pB * pA * pB ^ 2
        = pA ^ 2 * pB * pA ^ 3 * pB * pA * (pA ^ 2 * pB * pA ^ 2) by
          rw [← a2_b_a2_eq_b2]]
    rw [show pA ^ 2 * pB * pA ^ 3 * pB * pA * (pA ^ 2 * pB * pA ^ 2)
        = pA ^ 2 * pB * pA ^ 3 * pB * (pA * pA ^ 2) * pB * pA ^ 2 by group]
    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
  -- 3：aaa → b·a²·b（位置 3，rule3 反向；首 a³ 单块）＋幂合并
  _ = pA ^ 2 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 2 := by
    nth_rewrite 1 [← b_a2_b_eq_a3]
    rw [show pA ^ 2 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 3 * pB * pA ^ 2
        = pA ^ 2 * (pB * pB) * pA ^ 2 * (pB * pB) * pA ^ 3 * pB * pA ^ 2 by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
  -- 4：b²·a³ → a²·b（位置 6，rule1 反向；b²·a³ 单块）＋幂合并
  _ = pA ^ 2 * pB ^ 2 * pA ^ 4 * pB ^ 2 * pA ^ 2 := by
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 2
        = pA ^ 2 * pB ^ 2 * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pB * pA ^ 2 by group]
    rw [← a2_b_comm]
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2 * (pA ^ 2 * pB) * pB * pA ^ 2
        = pA ^ 2 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pB * pA ^ 2 by group]
    rw [show pA ^ 2 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pB * pA ^ 2
        = pA ^ 2 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * (pB * pB) * pA ^ 2 by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- 5：b²·a³ → a²·b（位置 2，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并
  _ = pA ^ 4 * pB * pA * pB ^ 2 * pA ^ 2 := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]
    rw [show pA ^ 2 * pB ^ 2 * (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2
        = pA ^ 2 * (pB ^ 2 * pA ^ 3) * pA * pB ^ 2 * pA ^ 2 by group]
    rw [← a2_b_comm]
    rw [show pA ^ 2 * (pA ^ 2 * pB) * pA * pB ^ 2 * pA ^ 2
        = (pA ^ 2 * pA ^ 2) * pB * pA * pB ^ 2 * pA ^ 2 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- 6：bb → a²·b·a²（位置 6，rule2 反向；b² 单块）＋幂合并
  _ = pA ^ 4 * pB * pA ^ 3 * pB * pA ^ 4 := by
    rw [← a2_b_a2_eq_b2]
    rw [show pA ^ 4 * pB * pA * (pA ^ 2 * pB * pA ^ 2) * pA ^ 2
        = pA ^ 4 * pB * (pA * pA ^ 2) * pB * (pA ^ 2 * pA ^ 2) by group]
    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- 7：aaa → b·a²·b（位置 5，rule3 反向；a³ 单块）＋幂合并
  _ = pA ^ 4 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 4 := by
    rw [← b_a2_b_eq_a3]
    rw [show pA ^ 4 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 4
        = pA ^ 4 * (pB * pB) * pA ^ 2 * (pB * pB) * pA ^ 4 by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
  -- 8：b²·a³ → a²·b（位置 8，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并
  _ = pA ^ 4 * pB ^ 2 * pA ^ 4 * pB * pA := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]
    rw [show (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * pB ^ 2 * (pA ^ 3 * pA)
        = (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pA by group]
    rw [← a2_b_comm]
    rw [show (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * (pA ^ 2 * pB) * pA
        = (pA ^ 3 * pA) * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pA by group]
    rw [show pA ^ 3 * pA = pA ^ 4 by rw [← pow_succ]]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- 9：a⁴·b²·a⁴ → a·b·a（位置 0-9，rule4 反向；跨三因子）
  _ = pA * pB * pA * pB * pA := by
    rw [← a_b_a_eq_a4_b2_a4]
lemma pA_mul_coset (i : Fin 12) :
    ∃ k : Fin 5, pA * cosetRep i = cosetRep (aTarget i) * pA ^ k.val := by
  fin_cases i
  · simpa [aTarget] using coset_a_0
  · simpa [aTarget] using coset_a_1
  · simpa [aTarget] using coset_a_2
  · simpa [aTarget] using coset_a_3
  · simpa [aTarget] using coset_a_4
  · simpa [aTarget] using coset_a_5
  · simpa [aTarget] using coset_a_6
  · simpa [aTarget] using coset_a_7
  · simpa [aTarget] using coset_a_8
  · simpa [aTarget] using coset_a_9
  · simpa [aTarget] using coset_a_10
  · simpa [aTarget] using coset_a_11

lemma pB_mul_coset (i : Fin 12) :
    ∃ k : Fin 5, pB * cosetRep i = cosetRep (bTarget i) * pA ^ k.val := by
  fin_cases i
  · simpa [bTarget] using coset_b_0
  · simpa [bTarget] using coset_b_1
  · simpa [bTarget] using coset_b_2
  · simpa [bTarget] using coset_b_3
  · simpa [bTarget] using coset_b_4
  · simpa [bTarget] using coset_b_5
  · simpa [bTarget] using coset_b_6
  · simpa [bTarget] using coset_b_7
  · simpa [bTarget] using coset_b_8
  · simpa [bTarget] using coset_b_9
  · simpa [bTarget] using coset_b_10
  · simpa [bTarget] using coset_b_11

-- 标准形 S := {cᵢ·aᵏ}
abbrev S (x : P) : Prop := ∃ p : Fin 12 × Fin 5, x = cosetRep p.1 * pA ^ p.2.val

lemma S_one : S 1 := by
  use (0, 0)
  simp [S, cosetRep]

lemma S_pA : S pA := by
  use (0, 1)
  simp [S, cosetRep]

lemma S_pB : S pB := by
  use (1, 0)
  simp [S, cosetRep]

-- S 对左乘 pA、pB 封闭
lemma S_mul_pA {x : P} (hx : S x) : S (pA * x) := by
  rcases hx with ⟨p, rfl⟩
  rcases pA_mul_coset p.1 with ⟨k, hk⟩
  rw [← mul_assoc, hk, mul_assoc]
  change S (cosetRep (aTarget p.1) * (pA ^ k.val * pA ^ p.2.val))
  rw [pA_pow_add_fin]
  use (aTarget p.1, k + p.2)

lemma S_mul_pB {x : P} (hx : S x) : S (pB * x) := by
  rcases hx with ⟨p, rfl⟩
  rcases pB_mul_coset p.1 with ⟨k, hk⟩
  rw [← mul_assoc, hk, mul_assoc]
  change S (cosetRep (bTarget p.1) * (pA ^ k.val * pA ^ p.2.val))
  rw [pA_pow_add_fin]
  use (bTarget p.1, k + p.2)

-- P 的每个元素 ∈ Submonoid.closure {pA, pB}（自由群归纳，生成元逆 = 正幂）
lemma P_mem_submonoid_closure (x : P) :
    x ∈ Submonoid.closure ({pA, pB} : Set P) := by
  refine (PresentedGroup.induction_on x
    (C := fun x : P => x ∈ Submonoid.closure ({pA, pB} : Set P) ∧
      x⁻¹ ∈ Submonoid.closure ({pA, pB} : Set P)) ?_).1
  intro z
  induction z with
  | one =>
      constructor
      · change 1 ∈ Submonoid.closure ({pA, pB} : Set P)
        exact Submonoid.one_mem _
      · change (1 : P)⁻¹ ∈ Submonoid.closure ({pA, pB} : Set P)
        simp [Submonoid.one_mem]
  | of i =>
      constructor
      · change PresentedGroup.of (rels := rels) i ∈ Submonoid.closure ({pA, pB} : Set P)
        fin_cases i
        · change pA ∈ Submonoid.closure ({pA, pB} : Set P)
          exact Submonoid.subset_closure (by simp)
        · change pB ∈ Submonoid.closure ({pA, pB} : Set P)
          exact Submonoid.subset_closure (by simp)
      · change (PresentedGroup.of (rels := rels) i)⁻¹ ∈ Submonoid.closure ({pA, pB} : Set P)
        fin_cases i
        · change pA⁻¹ ∈ Submonoid.closure ({pA, pB} : Set P)
          rw [pA_inv]
          have hpA : pA ∈ ({pA, pB} : Set P) := by simp
          exact Submonoid.pow_mem (Submonoid.closure ({pA, pB} : Set P)) (Submonoid.subset_closure hpA) 4
        · change pB⁻¹ ∈ Submonoid.closure ({pA, pB} : Set P)
          rw [pB_inv]
          have hpB : pB ∈ ({pA, pB} : Set P) := by simp
          exact Submonoid.pow_mem (Submonoid.closure ({pA, pB} : Set P)) (Submonoid.subset_closure hpB) 2
  | inv_of z ih =>
      constructor
      · rw [map_inv]
        exact ih.2
      · rw [map_inv, inv_inv]
        exact ih.1
  | mul z₁ z₂ ih₁ ih₂ =>
      constructor
      · rw [map_mul]
        exact Submonoid.mul_mem _ ih₁.1 ih₂.1
      · rw [map_mul, mul_inv_rev]
        exact Submonoid.mul_mem _ ih₂.2 ih₁.2

-- 幺半群闭包 = ⊤
lemma submonoid_closure_eq_top :
    Submonoid.closure ({pA, pB} : Set P) = ⊤ := by
  ext x
  simp [P_mem_submonoid_closure]

-- S 覆盖全群：∀ x, x ∈ S
lemma S_univ (x : P) : S x := by
  refine Submonoid.induction_of_closure_eq_top_left (s := ({pA, pB} : Set P)) ?_ x ?_ ?_
  · exact submonoid_closure_eq_top
  · exact S_one
  · intro y hy z hz
    simp at hy
    rcases hy with rfl | rfl
    · exact S_mul_pA hz
    · exact S_mul_pB hz

-- 标准形映射：P → Fin 12 × Fin 5（非计算，用选择公理）
noncomputable def std (x : P) : Fin 12 × Fin 5 :=
  Classical.choose (S_univ x)

lemma std_injective : Function.Injective std := by
  intro x y hxy
  have hx := Classical.choose_spec (S_univ x)
  have hy := Classical.choose_spec (S_univ y)
  rw [hx, hy]
  unfold std at hxy
  rw [hxy]

-- |P| ≤ 60
lemma card_P_le_60 : Nat.card P ≤ 60 := by
  letI : Fintype P := Fintype.ofInjective std std_injective
  rw [Nat.card_eq_fintype_card]
  have hle : Fintype.card P ≤ Fintype.card (Fin 12 × Fin 5) :=
    Fintype.card_le_of_injective std std_injective
  norm_num at hle
  exact hle

-- 60 ≤ |P|（φ 满射 → 单射 G → P）
lemma φ_surjective : Function.Surjective φ := by
  intro g
  have hg : g ∈ φ.range := by
    rw [φ_range_top]
    trivial
  simpa using hg

noncomputable def φ_preimage (g : G) : P :=
  Classical.choose (φ_surjective g)

lemma φ_preimage_injective : Function.Injective φ_preimage := by
  intro g₁ g₂ h
  have h₁ := Classical.choose_spec (φ_surjective g₁)
  have h₂ := Classical.choose_spec (φ_surjective g₂)
  rw [← h₁, ← h₂]
  exact congrArg φ h

lemma card_60_le_P : 60 ≤ Nat.card P := by
  letI : Fintype P := Fintype.ofInjective std std_injective
  have hle : Fintype.card G ≤ Fintype.card P :=
    Fintype.card_le_of_injective φ_preimage φ_preimage_injective
  have hG : Fintype.card G = 60 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_G
  rw [Nat.card_eq_fintype_card]
  rw [hG] at hle
  exact hle

-- 呈现完备性：|P| = 60
lemma card_P : Nat.card P = 60 :=
  le_antisymm card_P_le_60 card_60_le_P

-- ============ #3d：二十面体表示下降（φ 满射 + |P|=|G|=60 → 同构） ============

noncomputable instance : Fintype P := Fintype.ofInjective std std_injective

-- φ_preimage 是 φ 的左逆（由 φ_preimage 单射 + card G = card P = 60 得双射）
lemma φ_preimage_leftInverse : Function.LeftInverse φ_preimage φ := by
  intro x
  have hbij : Function.Bijective φ_preimage := by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · exact φ_preimage_injective
    · rw [← Nat.card_eq_fintype_card (α := G), ← Nat.card_eq_fintype_card (α := P), card_G, card_P]
  rcases hbij.2 x with ⟨g, hg⟩
  calc
    φ_preimage (φ x) = φ_preimage (φ (φ_preimage g)) := by rw [← hg]
    _ = φ_preimage g := congrArg φ_preimage (Classical.choose_spec (φ_surjective g))
    _ = x := hg

lemma φ_injective : Function.Injective φ := by
  intro x y hxy
  rw [← φ_preimage_leftInverse x, ← φ_preimage_leftInverse y, hxy]

-- φ 的逆同态：G →* P（用 φ 单射 + choose_spec 逐点验证）
noncomputable def ψ : G →* P where
  toFun := φ_preimage
  map_one' := by
    apply φ_injective
    calc
      φ (φ_preimage 1) = 1 := Classical.choose_spec (φ_surjective 1)
      _ = φ 1 := φ.map_one.symm
  map_mul' g₁ g₂ := by
    apply φ_injective
    calc
      φ (φ_preimage (g₁ * g₂)) = g₁ * g₂ := Classical.choose_spec (φ_surjective (g₁ * g₂))
      _ = φ (φ_preimage g₁) * φ (φ_preimage g₂) := by
        congr 1
        · exact (Classical.choose_spec (φ_surjective g₁)).symm
        · exact (Classical.choose_spec (φ_surjective g₂)).symm
      _ = φ (φ_preimage g₁ * φ_preimage g₂) := (φ.map_mul (φ_preimage g₁) (φ_preimage g₂)).symm

-- 呈现群 P 上的矩阵表示 → 线性表示（GL → LinearMap）
noncomputable def ρP : Representation ℂ P (Fin 3 → ℂ) :=
  ((Units.coeHom (M := (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))).comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom)).comp icosahedralPsi

-- 沿同构 ψ : G →* P 拉回为 G 上的表示
noncomputable def ρG : Representation ℂ G (Fin 3 → ℂ) := ρP.comp ψ

/-- A₅ 的 3 维二十面体表示（显式矩阵构造，见文件头实现路径）。 -/
def icosahedralRep : FDRep ℂ G := FDRep.of ρG

/-- 维数 = 3。 -/
theorem finrank_icosahedralRep : Module.finrank ℂ icosahedralRep = 3 := by
  change Module.finrank ℂ (Fin 3 → ℂ) = 3
  simp

/- ======================================================================== -/
-- #5/#6：5 阶元特征标值 = 黄金比；特征标值全在 Q(√5)
--
-- 数学路线（#3b 注释 419-431）：
--   S = ψ(s)、T = ψ(t)；χ(s) = tr S = φ̄、χ(s²) = tr A = φ（两个 5-共轭类）。
--   tr(S²) = 3g² - c² - 1/4 = α（g = (1+√5)/4、c = (√5-1)/4）。
--   #5：取 5 阶元 sG²，χ(sG²) = tr(S²) = α。
--   #6：候选值 {3, -1, 0, φ, φ̄} 全在 goldenToComplex 像里（代数骨架已完成），
--       这里补 α 侧五黄金引理与各共轭类代表元的 char 值。
/- ======================================================================== -/

-- 五黄金引理（ℂ 侧，对应 GoldenInt 的 phi_sq / phi_mul_phi_bar / phi_add_phi_bar / phi_bar_eq）

/-- α + (1-α) = 1（φ + φ̄ = 1）。 -/
lemma alpha_add_alpha_bar : alpha + (1 - alpha) = 1 := by
  ring

/-- α·(1-α) = -1（φ·φ̄ = -1）。 -/
lemma alpha_mul_alpha_bar : alpha * (1 - alpha) = -1 := by
  have h := alpha_sq
  calc
    alpha * (1 - alpha) = alpha - alpha * alpha := by ring
    _ = alpha - (1 + alpha) := by rw [h]
    _ = -1 := by ring

/-- (1-α)² = 2 - α（φ̄² = 2 - φ）。 -/
lemma alpha_bar_sq : (1 - alpha) ^ 2 = 2 - alpha := by
  have h := alpha_sq
  calc
    (1 - alpha) ^ 2 = (1 - alpha) * (1 - alpha) := by rw [pow_two]
    _ = 1 - 2 * alpha + alpha * alpha := by ring
    _ = 1 - 2 * alpha + (1 + alpha) := by rw [h]
    _ = 2 - alpha := by ring

/-- 2α - 1 = √5（连接数论侧）。 -/
lemma alpha_two_mul_sub_one : 2 * alpha - 1 = (Real.sqrt 5 : ℂ) := by
  unfold alpha
  field_simp
  ring

-- 各共轭类代表元的矩阵迹

/-- tr(S) = φ̄ = 1 - α。 -/
lemma trace_icosahedralS : icosahedralS.trace = 1 - alpha := by
  unfold Matrix.trace
  simp [icosahedralS, c5, g5, Fin.sum_univ_succ]
  unfold alpha
  ring_nf

/-- tr(S²) = α。 -/
lemma trace_icosahedralS_sq : (icosahedralS ^ 2).trace = alpha := by
  rw [pow_two]
  unfold Matrix.trace
  simp [Matrix.mul_apply, Fin.sum_univ_succ, icosahedralS, c5, g5]
  unfold alpha
  ring_nf
  norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four]
  ring_nf

/-- tr(T) = 0。 -/
lemma trace_icosahedralT : icosahedralT.trace = 0 := by
  unfold Matrix.trace
  simp [icosahedralT, Fin.sum_univ_succ]

/-- tr(S²T) = -1（2 阶元）。 -/
lemma trace_icosahedralS2T : (icosahedralS ^ 2 * icosahedralT).trace = -1 := by
  rw [pow_two]
  unfold Matrix.trace
  simp [Matrix.mul_apply, Fin.sum_univ_succ, icosahedralS, icosahedralT, c5, g5]
  ring_nf
  norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four]

-- ψ 拉回：ψ : G →* P 是 φ 的逆同态

/-- ψ(sG) = pA。 -/
lemma psi_sG : ψ sG = pA := by
  have hφ : φ pA = sG := by
    simp [φ, pA]
  calc
    ψ sG = φ_preimage sG := rfl
    _ = φ_preimage (φ pA) := by rw [← hφ]
    _ = pA := φ_preimage_leftInverse pA

/-- ψ(tG) = pB。 -/
lemma psi_tG : ψ tG = pB := by
  have hφ : φ pB = tG := by
    simp [φ, pB]
  calc
    ψ tG = φ_preimage tG := rfl
    _ = φ_preimage (φ pB) := by rw [← hφ]
    _ = pB := φ_preimage_leftInverse pB

-- ρP 在生成元上的矩阵展开（ρP = coeHom ∘ toLin ∘ icosahedralPsi）

/-- ρP(pA) = 矩阵左乘 S 的线性映射。 -/
lemma ρP_pA_eq : ρP pA = Matrix.toLin' icosahedralS := by
  unfold ρP
  change Units.coeHom (M := (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (Matrix.GeneralLinearGroup.toLin (icosahedralPsi pA)) = Matrix.toLin' icosahedralS
  simp [icosahedralPsi, pA, Matrix.GeneralLinearGroup.coe_toLin, unitS, Matrix.toLin'_apply']

/-- ρP(pB) = 矩阵左乘 T 的线性映射。 -/
lemma ρP_pB_eq : ρP pB = Matrix.toLin' icosahedralT := by
  unfold ρP
  change Units.coeHom (M := (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (Matrix.GeneralLinearGroup.toLin (icosahedralPsi pB)) = Matrix.toLin' icosahedralT
  simp [icosahedralPsi, pB, Matrix.GeneralLinearGroup.coe_toLin, unitT, Matrix.toLin'_apply']

/-- ρP(pA²) = 矩阵左乘 S² 的线性映射（ρP 保幂 + toLin' 保幂）。 -/
lemma ρP_pA_sq_eq : ρP (pA ^ 2) = Matrix.toLin' (icosahedralS ^ 2) := by
  rw [map_pow, ρP_pA_eq]
  rw [← Matrix.toLin'_pow]

/-- ρP(pA²·pB) = 矩阵左乘 S²T 的线性映射。 -/
lemma ρP_pA_sq_mul_pB_eq : ρP (pA ^ 2 * pB) = Matrix.toLin' (icosahedralS ^ 2 * icosahedralT) := by
  rw [map_mul, ρP_pA_sq_eq, ρP_pB_eq]
  change Matrix.toLin' (icosahedralS ^ 2) ∘ₗ Matrix.toLin' icosahedralT =
    Matrix.toLin' (icosahedralS ^ 2 * icosahedralT)
  rw [← Matrix.toLin'_mul]

-- 各共轭类代表元的特征标值

/-- χ(1) = 3。 -/
lemma char_one : icosahedralRep.character (1 : G) = 3 := by
  rw [FDRep.char_one, finrank_icosahedralRep]
  norm_num

/-- χ(sG) = φ̄ = 1 - α（5 阶共轭类 I）。 -/
lemma char_sG : icosahedralRep.character sG = 1 - alpha := by
  calc
    icosahedralRep.character sG = LinearMap.trace ℂ (Fin 3 → ℂ) (ρG sG) := by
        rw [icosahedralRep, FDRep.character, FDRep.of_ρ']
    _ = LinearMap.trace ℂ (Fin 3 → ℂ) (ρP pA) := by
        congr 1
        calc
          ρG sG = ρP (ψ sG) := by simp [ρG]
          _ = ρP pA := by rw [psi_sG]
    _ = icosahedralS.trace := by
        rw [ρP_pA_eq]
        simp
    _ = 1 - alpha := trace_icosahedralS

/-- χ(tG) = 0（3 阶共轭类）。 -/
lemma char_tG : icosahedralRep.character tG = 0 := by
  calc
    icosahedralRep.character tG = LinearMap.trace ℂ (Fin 3 → ℂ) (ρG tG) := by
        rw [icosahedralRep, FDRep.character, FDRep.of_ρ']
    _ = LinearMap.trace ℂ (Fin 3 → ℂ) (ρP pB) := by
        congr 1
        calc
          ρG tG = ρP (ψ tG) := by simp [ρG]
          _ = ρP pB := by rw [psi_tG]
    _ = icosahedralT.trace := by
        rw [ρP_pB_eq]
        simp
    _ = 0 := trace_icosahedralT

/-- χ(sG²) = α（5 阶共轭类 II）。 -/
lemma char_sG_sq : icosahedralRep.character (sG ^ 2) = alpha := by
  calc
    icosahedralRep.character (sG ^ 2) = LinearMap.trace ℂ (Fin 3 → ℂ) (ρG (sG ^ 2)) := by
        rw [icosahedralRep, FDRep.character, FDRep.of_ρ']
    _ = LinearMap.trace ℂ (Fin 3 → ℂ) (ρP (pA ^ 2)) := by
        congr 1
        calc
          ρG (sG ^ 2) = ρP (ψ (sG ^ 2)) := by simp [ρG]
          _ = ρP ((ψ sG) ^ 2) := by rw [map_pow]
          _ = ρP (pA ^ 2) := by rw [psi_sG]
    _ = (icosahedralS ^ 2).trace := by
        rw [ρP_pA_sq_eq, Matrix.trace_toLin'_eq]
    _ = alpha := trace_icosahedralS_sq

/-- χ(sG²·tG) = -1（2 阶共轭类）。 -/
lemma char_sG_sq_tG : icosahedralRep.character (sG ^ 2 * tG) = -1 := by
  calc
    icosahedralRep.character (sG ^ 2 * tG) = LinearMap.trace ℂ (Fin 3 → ℂ) (ρG (sG ^ 2 * tG)) := by
        rw [icosahedralRep, FDRep.character, FDRep.of_ρ']
    _ = LinearMap.trace ℂ (Fin 3 → ℂ) (ρP (pA ^ 2 * pB)) := by
        congr 1
        calc
          ρG (sG ^ 2 * tG) = ρP (ψ (sG ^ 2 * tG)) := by simp [ρG]
          _ = ρP (ψ (sG ^ 2) * ψ tG) := by rw [map_mul]
          _ = ρP ((ψ sG) ^ 2 * ψ tG) := by rw [map_pow]
          _ = ρP (pA ^ 2 * pB) := by rw [psi_sG, psi_tG]
    _ = (icosahedralS ^ 2 * icosahedralT).trace := by
        rw [ρP_pA_sq_mul_pB_eq, Matrix.trace_toLin'_eq]
    _ = -1 := trace_icosahedralS2T

/-- #5：存在 5 阶元 g，χ(g) = α。 -/
lemma exists_five_order_char_phi : ∃ g : G, orderOf g = 5 ∧ icosahedralRep.character g = alpha := by
  refine ⟨sG ^ 2, ?_, ?_⟩
  · rw [orderOf_pow, orderOf_sG]
    norm_num
  · exact char_sG_sq

/- ======================================================================== -/
-- #6：全部特征标值 ∈ Q(√5)（即落在 goldenToComplex 的像内）。
-- A₅ 的五个共轭类代表元 {1, sG, tG, sG², sG²·tG} 上的特征标值分别为
-- {3, φ̄=1-α, 0, φ=α, -1}。
/- ======================================================================== -/

/-- #6：A₅ 的全部特征标值 ∈ Q(√5)：
    每个共轭类代表元的 χ 值都落在 goldenToComplex 的像内。 -/
lemma char_values_in_Q5 :
    ∃ a : GoldenInt, goldenToComplex a = icosahedralRep.character (1 : G) ∧
    ∃ b : GoldenInt, goldenToComplex b = icosahedralRep.character sG ∧
    ∃ c : GoldenInt, goldenToComplex c = icosahedralRep.character tG ∧
    ∃ d : GoldenInt, goldenToComplex d = icosahedralRep.character (sG ^ 2) ∧
    ∃ e : GoldenInt, goldenToComplex e = icosahedralRep.character (sG ^ 2 * tG) := by
  refine ⟨3, ?_, ⟨GoldenInt.phi_bar, ?_, ⟨0, ?_, ⟨GoldenInt.phi, ?_, ⟨-1, ?_⟩⟩⟩⟩⟩
  · rw [goldenToComplex_three, char_one]
  · rw [goldenToComplex_phi_bar, char_sG]
  · rw [goldenToComplex_zero, char_tG]
  · rw [goldenToComplex_phi, char_sG_sq]
  · rw [goldenToComplex_neg_one, char_sG_sq_tG]

/- ======================================================================== -/
-- #4 前置：表示的忠实性。ρG 的核为 ⊥（即 ρG 单射）。
-- 论证：ker 是 G 的正规子群；G = A₅ 是单群 ⟹ ker = ⊥ 或 ⊤；
-- 取 g = sG，ρG sG = toLin' S ≠ 1（S 的 (0,1) 分量为 1/2，单位阵为 0），故 ker ≠ ⊤。
-- 这条不依赖共轭类结构，是 #4（不可约性）的踏脚石。
/- ======================================================================== -/

/-- 把 ρG 包装成幺半群同态 G →* End(ℂ³)，以便调用 `MonoidHom.ker`。 -/
noncomputable def rhoGMonoidHom : G →* ((Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) where
  toFun := ρG
  map_one' := ρG.map_one'
  map_mul' := ρG.map_mul'

/-- 二十面体矩阵 S ≠ 单位阵：其 (0,1) 分量为 1/2，而单位阵该位置为 0。 -/
lemma icosahedralS_ne_one : icosahedralS ≠ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [icosahedralS] at h01

/-- ρG(sG) ≠ 1：ρG sG = toLin' S，作用在基向量 e₁ 上的第 0 分量为 1/2，恒等映射给 0。 -/
lemma ρG_sG_ne_one (h : ρG sG = 1) : False := by
  have hρ : ρG sG = Matrix.toLin' icosahedralS := by simp [ρG, psi_sG, ρP_pA_eq]
  rw [hρ] at h
  have hv := LinearMap.congr_fun h (Pi.single (1 : Fin 3) (1 : ℂ))
  have h0 := congrFun hv 0
  simp [Matrix.toLin'_apply, icosahedralS, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Pi.single] at h0

/-- **表示的忠实性**：ρG 的核为 ⊥。等价说法：A₅ 的 3 维二十面体表示是忠实的。 -/
lemma rhoG_ker_eq_bot : MonoidHom.ker rhoGMonoidHom = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.normal_ker rhoGMonoidHom) with h | h
  · exact h
  · exfalso
    have hs : sG ∈ MonoidHom.ker rhoGMonoidHom := by rw [h]; exact Subgroup.mem_top sG
    exact ρG_sG_ne_one ((MonoidHom.mem_ker).mp hs)

/-- ρG 单射（`ker = ⊥` 的常用等价形式）。 -/
lemma ρG_injective : Function.Injective ρG := by
  have h : Function.Injective rhoGMonoidHom :=
    (MonoidHom.ker_eq_bot_iff rhoGMonoidHom).mp rhoG_ker_eq_bot
  exact h


/-- χ(sG⁻¹) = ᾱ = 1 - α（sG⁻¹ = sG⁴）。 -/
theorem char_sG_inv : icosahedralRep.character (sG⁻¹) = 1 - alpha := by
  have h5 : sG ^ 5 = 1 := by
    have := pow_orderOf_eq_one sG
    rwa [orderOf_sG] at this
  have hinv : sG⁻¹ = sG ^ 4 := by
    have h4 : sG ^ 4 * sG = 1 := by
      rw [← pow_succ, h5]
    exact inv_eq_of_mul_eq_one_left h4
  calc
    icosahedralRep.character (sG⁻¹) =
        LinearMap.trace ℂ (Fin 3 → ℂ) (ρG (sG⁻¹)) := by
      rw [icosahedralRep, FDRep.character, FDRep.of_ρ']
    _ = LinearMap.trace ℂ (Fin 3 → ℂ) (ρP (pA ^ 4)) := by
      congr 1
      calc
        ρG (sG⁻¹) = ρG (sG ^ 4) := by rw [hinv]
        _ = ρP (ψ (sG ^ 4)) := by simp [ρG]
        _ = ρP ((ψ sG) ^ 4) := by rw [map_pow]
        _ = ρP (pA ^ 4) := by rw [psi_sG]
    _ = (icosahedralS ^ 4).trace := by
      have hto : (Matrix.toLin' (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)) ^ 4
          = Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 4) := by
        rw [show (4 : ℕ) = 2 + 2 from by norm_num]
        rw [pow_add]
        rw [pow_two]
        rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ (2 + 2)
            = (icosahedralS ^ 2) * (icosahedralS ^ 2) from by rw [pow_add]]
        rw [Matrix.toLin'_mul]
        rw [show (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 2
            = icosahedralS * icosahedralS from
              pow_two (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)]
        rw [Matrix.toLin'_mul]
        rfl
      rw [show ρP (pA ^ 4) =
          Matrix.toLin' ((icosahedralS : Matrix (Fin 3) (Fin 3) ℂ) ^ 4) from by
        rw [map_pow, ρP_pA_eq]
        rw [hto]]
      exact Matrix.trace_toLin'_eq _
    _ = 1 - alpha := by
      rw [show (4 : ℕ) = 2 + 2 from by norm_num, pow_add]
      rw [pow_two (icosahedralS : Matrix (Fin 3) (Fin 3) ℂ)]
      unfold Matrix.trace
      simp [Fin.sum_univ_succ, icosahedralS, c5, g5]
      unfold alpha
      ring_nf
      norm_num [sqrt5_sq, sqrt5_cube, sqrt5_four]
      ring_nf

/-- 共轭元有相同的特征标值（`char_conj` 的 `IsConj` 形式）。 -/
theorem char_eq_of_isConj (g h : G) (hh : IsConj g h) :
    icosahedralRep.character h = icosahedralRep.character g := by
  obtain ⟨c, hc⟩ := hh
  have h1 : h * (↑c : ↥G) * (↑c : ↥G)⁻¹ = h := by
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have h2 : h * (↑c : ↥G) * (↑c : ↥G)⁻¹ = (↑c : ↥G) * g * (↑c : ↥G)⁻¹ := by
    rw [← hc]
  -- hc : (↑c) * g = h * (↑c)
  have hcy : h = (↑c : ↥G) * g * (↑c : ↥G)⁻¹ := h1.symm.trans h2
  rw [hcy]
  exact FDRep.char_conj icosahedralRep g (↑c)
