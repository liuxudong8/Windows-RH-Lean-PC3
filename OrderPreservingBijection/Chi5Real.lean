import OrderPreservingBijection.stage_3
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# χ₅ 的实性（`lfun_conj_symm` 证明第 ① 步）

目标：`χ₅` 作为 `DirichletCharacter ℂ 5` 的取值全部落在 ℝ 内（虚部 0）。
这是 `L(conj s) = conj (L s)` 的第一块砖：`1 < re s` 上的 Dirichlet 级数系数为实，
等价于 `χ₅` 的每个取值 `im = 0`。

结论结构：
1. `chi5UnitFun_eq_one_or_neg_one`：单位群上的取值只能是 `1` 或 `-1`（由 `chi5UnitFun` 的三分支定义直接给出）；
2. `chi5Dirichlet_eq_unit`：单位点上 `χ₅ = χ₅UnitFun`（`MulChar.ofUnitHom_coe` + `IsUnit.unit` 的可定义相等）；
3. `chi5Dirichlet_apply_im_zero`：单位点取值 ±1、非单位点为 `0`，两类虚部皆为 0。
-/

namespace OrderPreservingBijection

/-- `chi5UnitFun` 的取值只能是 `1` 或 `-1`（`Units ℂ` 里）。 -/
lemma chi5UnitFun_eq_one_or_neg_one (u : Units (ZMod 5)) :
    chi5UnitFun u = 1 ∨ chi5UnitFun u = -1 := by
  unfold chi5UnitFun
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- 单位点上 `χ₅` 就是 `chi5UnitFun`（`Units ℂ` 口径）。 -/
lemma chi5Dirichlet_eq_unit (u : Units (ZMod 5)) :
    chi5Dirichlet (u : ZMod 5) = (chi5UnitFun u : Units ℂ) := by
  unfold chi5Dirichlet
  exact MulChar.ofUnitHom_coe chi5UnitHom u

/-- **`χ₅` 的模不超过 1**：单位点取 ±1、非单位点取 0，故 `‖χ₅(x)‖ ≤ 1`。
    （供素数项 `Λ(n)χ₅(n)` 的粗界使用：`|Λχ₅| ≤ Λ`。） -/
theorem chi5Dirichlet_norm_le_one (x : ZMod 5) : ‖chi5Dirichlet x‖ ≤ 1 := by
  classical
  by_cases hx : IsUnit x
  · show ‖chi5Dirichlet (hx.unit : ZMod 5)‖ ≤ 1
    rw [chi5Dirichlet_eq_unit hx.unit]
    rcases chi5UnitFun_eq_one_or_neg_one hx.unit with h | h
    · rw [h]; simp
    · rw [h]; simp
  · rw [MulChar.map_nonunit chi5Dirichlet hx]
    simp

/-- **χ₅ 的实性**：`DirichletCharacter ℂ 5` 的取值虚部恒为 0。 -/
theorem chi5Dirichlet_apply_im_zero (x : ZMod 5) : (chi5Dirichlet x).im = 0 := by
  classical
  by_cases hx : IsUnit x
  · show (chi5Dirichlet (hx.unit : ZMod 5)).im = 0
    rw [chi5Dirichlet_eq_unit hx.unit]
    show ((chi5UnitFun hx.unit : Units ℂ) : ℂ).im = 0
    rcases chi5UnitFun_eq_one_or_neg_one hx.unit with h | h
    · rw [h]; simp
    · rw [h]; simp
  · rw [MulChar.map_nonunit chi5Dirichlet hx]
    simp

/-- 收口形式（供 `LFun` 共轭步骤使用）：对任意自然数 `n`，`χ₅(n)` 的虚部为 0。 -/
theorem chi5Dirichlet_im_zero (n : ℕ) : (chi5Dirichlet (n : ZMod 5)).im = 0 :=
  chi5Dirichlet_apply_im_zero _

/-- 推论：`χ₅(n)` 的虚部为零 ⟹ `χ₅(n) = (χ₅(n)).re`（实数性，供级数系数实性使用）。 -/
theorem chi5Dirichlet_eq_re (n : ℕ) :
    chi5Dirichlet (n : ZMod 5) = ((chi5Dirichlet (n : ZMod 5)).re : ℂ) := by
  have h := chi5Dirichlet_im_zero n
  refine Complex.ext ?_ ?_
  · simp
  · simpa using h

/-- `χ₅(2) = -1`（`2` 在 `ZMod 5` 中为单位：`2 * 3 = 6 = 1`）。 -/
theorem chi5Dirichlet_two : chi5Dirichlet (2 : ZMod 5) = -1 := by
  let u : Units (ZMod 5) := ⟨2, 3, by decide, by decide⟩
  have hu : (u : ZMod 5) = 2 := rfl
  have hval : chi5Dirichlet (u : ZMod 5) = (chi5UnitFun u : ℂ) := chi5Dirichlet_eq_unit u
  show chi5Dirichlet (u : ZMod 5) = (-1 : ℂ)
  rw [hval, chi5UnitFun_val u]
  have hval2 : (u : ZMod 5).val = 2 := by rw [hu]; decide
  rw [hval2]
  have hchi : (chi5 2 : ℂ) = (-1 : ℂ) := by
    have h : chi5 2 = -1 := by decide
    rw [h]
    norm_num
  exact hchi

/-- **χ₅ 非平凡**：`χ₅ ≠ 1`（截点 `n = 2` 处取 `-1`）。
    这是 `differentiableAt_LFunction` 在 `s = 1` 可用的前提（`χ₅ ≠ 1` 时 L 在 1 处全纯）。 -/
theorem chi5Dirichlet_ne_one : chi5Dirichlet ≠ 1 := by
  intro h
  have h2 := chi5Dirichlet_two
  rw [h] at h2
  have hunit : IsUnit (2 : ZMod 5) := ⟨⟨2, 3, by decide, by decide⟩, rfl⟩
  rw [MulChar.one_apply hunit] at h2
  norm_num at h2

/-- **χ₅ 的 L 函数全平面全纯**：`χ₅ ≠ 1` ⟹ mathlib `differentiable_LFunction` 直接落地。
    这是第 ③ 步（解析延拓唯一性）在 `s = 1` 处的关键前提。 -/
theorem differentiable_LFunction_chi5 :
    Differentiable ℂ (DirichletCharacter.LFunction chi5Dirichlet) :=
  DirichletCharacter.differentiable_LFunction chi5Dirichlet_ne_one

end OrderPreservingBijection
