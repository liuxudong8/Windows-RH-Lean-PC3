/-
第 1 条：陈述层对齐
把我们的条件定理 `RHSpectralDuality.riemann_hypothesis`（仅在开条带 0 < Re s < 1 内断言、
且多带一个 `f : MollifiedTestFunction` 参数）升级为 Mathlib 标准形 `RiemannHypothesis`：

  ∀ s, riemannZeta s = 0 → (¬∃ n, s = -2 * (n+1)) → s ≠ 1 → s.re = 1/2

三条支路：
  · 开条带：直接用我们的定理（丢弃 f 参数，内部取 `nonempty_mollified_test_function`）；
  · Re s ≥ 1：Mathlib `riemannZeta_ne_zero_of_one_le_re` 直接排除；
  · Re s ≤ 0 且非平凡：用 completed ζ 的对称性 + `Gammaℝ` 零点刻画排除（见下）。
-/
import OrderPreservingBijection.stage_4
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

namespace RHSpectralDuality

open Complex OrderPreservingBijection

/-- `Re s ≤ 0` 上 ζ 无零点的第三个支路。

    链条：`ζ s = Λ s / Γℝ s`（`riemannZeta_def_of_ne_zero`），而
    `Λ s = Λ (1 - s)`（`completedRiemannZeta_one_sub`）。
    由 `Re s ≤ 0` 得 `Re (1 - s) ≥ 1`，故 `ζ (1 - s) ≠ 0`（`riemannZeta_ne_zero_of_one_le_re`）
    且 `Γℝ (1 - s) ≠ 0`（`Gammaℝ_ne_zero_of_re_pos`），于是 `Λ (1 - s) ≠ 0`，即 `Λ s ≠ 0`。
    再由 `Γℝ s ≠ 0`（否则 `s = -2n` 属平凡零点，与 `htriv` 冲突；`s = 0` 由 `ζ 0 = -1/2` 排除）
    得 `ζ s ≠ 0`，与 `hz` 矛盾。 -/
lemma no_zero_of_nonpos_re (s : ℂ) (hz : _root_.riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) (hne1 : s ≠ 1) (hre : s.re ≤ 0) : False := by
  -- s ≠ 0：ζ 0 = -1/2
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [_root_.riemannZeta_zero] at hz
    norm_num at hz
  -- Γℝ s ≠ 0：其零点恰为 s = -2n，即平凡零点（n = 0 时 s = 0）
  have hG : Gammaℝ s ≠ 0 := by
    intro hGs
    rw [Gammaℝ_eq_zero_iff] at hGs
    obtain ⟨n, hn⟩ := hGs
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact hs0 (by rw [hn, h0]; norm_num)
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact htriv ⟨k, by rw [hn, hk]; push_cast; ring⟩
  -- Re (1 - s) = 1 - Re s ≥ 1
  have hre1 : (1 - s).re = 1 - s.re := by simp
  -- Λ (1 - s) ≠ 0
  have h1s0 : (1 - s) ≠ 0 := by
    intro h
    have : (1 - s).re = 0 := by rw [h]; simp
    linarith
  have hΓ1 : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ1 : _root_.riemannZeta (1 - s) ≠ 0 :=
    _root_.riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hΛ1 : completedRiemannZeta (1 - s) ≠ 0 := by
    have hmul : completedRiemannZeta (1 - s)
        = _root_.riemannZeta (1 - s) * Gammaℝ (1 - s) := by
      rw [_root_.riemannZeta_def_of_ne_zero h1s0]
      field_simp
    rw [hmul]
    exact mul_ne_zero hζ1 hΓ1
  -- 对称性：Λ s = Λ (1 - s)
  have hΛs : completedRiemannZeta s ≠ 0 := by
    rw [← completedRiemannZeta_one_sub s]
    exact hΛ1
  -- ζ s = Λ s / Γℝ s，故 ζ s ≠ 0
  rw [_root_.riemannZeta_def_of_ne_zero hs0] at hz
  have hzero : completedRiemannZeta s = 0 := by
    have := (div_eq_iff hG).mp hz
    simpa using this
  exact hΛs hzero

/-- 对齐版主定理：我们的谱对偶条件 ⟹ Mathlib 标准 `RiemannHypothesis`。
    与 `riemann_hypothesis` 的区别：结论换成标准形、`f` 参数已消除。 -/
theorem riemann_hypothesis_std
    (h_duality : ∀ (f : MollifiedTestFunction),
      spectralSum f.toTestFunction = nontrivialZeroSum f.toTestFunction)
    (h_win : UniformSupport) : RiemannHypothesis := by
  intro s hz htriv hne1
  obtain ⟨f⟩ := nonempty_mollified_test_function
  rcases lt_trichotomy s.re 0 with hlt0 | heq0 | hgt0
  · exact (no_zero_of_nonpos_re s hz htriv hne1 (le_of_lt hlt0)).elim
  · exact (no_zero_of_nonpos_re s hz htriv hne1 (le_of_eq heq0)).elim
  · by_cases hlt1 : s.re < 1
    · exact riemann_hypothesis h_duality h_win f s hz hgt0 hlt1
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re (not_lt.mp hlt1))

end RHSpectralDuality
