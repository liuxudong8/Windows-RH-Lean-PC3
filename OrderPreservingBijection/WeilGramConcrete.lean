/-
Weil 二次型 Gram 矩阵的**可算形式**：素数侧 Σ_p (log p) ⟨φ_j, φ_k⟩_p + 零点侧 ‖φ̂_j‖² 的解析上界。

本文件兑现 stage_4 里 `weilGramMatrix hz hp` 的两个抽象入参：
* `hp` 不再是自由变量，而是真的 `∑_{p ∈ primesBelow N} (log p) · ⟨φ_j, φ_k⟩_p`；
* `hz_j` 不再是自由变量，而是 `∑_{ρ ∈ S} ‖φ̂_j(ρ)‖²`，并给出 `‖φ̂_j‖²` 的解析上界。

口径（必须与正文一起读，不得省略）：
1. **局部内积的替代**：真正的 `⟨φ_j, φ_k⟩_p` 是 ℚ_p^* 上对 Haar 测度的积分。
   mathlib 有 p 进数（`Padic`）但没有 p 进 Haar 测度的测度论接口，
   故本文件用显式权 `p^{-x} = exp(-x log p)` 在 `[0,1]` 上的积分作为局部权口径。
   这在数学上就是局部分支的乘法权（`p^{-x}` 是 `p` 进绝对值 `p^{-v}` 的阿基米德化写法），
   但它**不是** Haar 测度本身，这是本侧口径的硬边界。
2. **素数侧是有限截断**：`primesBelow N`，`N` 是显式截断参数；不取无穷和。
3. **零点侧是有限截断 + 对角**：`S : Finset ℂ` 只装 |Im ρ| ≤ T 的那部分零点，
   且只取对角 `‖φ̂_j(ρ)‖²`，`j ≠ k` 交叉项仍缺（stage_4 已声明这一点）。
4. `‖φ̂_j(ρ)‖²` 的上界是标准的：相位移位不改变 L¹ 范数到 `exp ‖ρ‖` 的倍数
   （`x ∈ [0,1]` 上相位 `I·ρ·x` 的实部不超过 `‖ρ‖`）。
-/

import OrderPreservingBijection.stage_4
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open Matrix

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace RHSpectralDuality

/-! ### 一、区间积分与共轭交换

`p` 进局部权是实值的，所以局部 Gram 的共轭对称只需要「区间积分与 `star` 交换」这一条。
它由 `integral_conj` 直接给出（注意该引理在 mathlib 里是**根命名空间** `integral_conj`，
不是 `MeasureTheory.integral_conj`）。 -/

theorem intervalIntegral_star (f : ℝ → ℂ) :
    (∫ x in (0 : ℝ)..1, star (f x)) = star (∫ x in (0 : ℝ)..1, f x) := by
  simp only [RCLike.star_def]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact integral_conj

/-! ### 二、素数次局部内积 `⟨φ_j, φ_k⟩_p` -/

/-- 局部权 `p^{-x} = exp(-x log p)`，以 `ℂ` 值给出（其值在实轴上，故对 `star` 不变）。 -/
noncomputable def localWeight (p : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (-(x * Real.log (p : ℝ))) : ℝ) : ℂ)

/-- 实值复数常量对 `star` 不变。 -/
theorem ofReal_star (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := by
  rw [RCLike.star_def]
  exact Complex.conj_ofReal r

/-- 局部权对 `star` 不变。 -/
theorem localWeight_star (p : ℕ) (x : ℝ) : star (localWeight p x) = localWeight p x := by
  rw [localWeight]
  exact ofReal_star _

/-- 局部内积（口径见文件头第 1 条）：`∫₀¹ p^{-x} φ(x) \overline{ψ(x)} dx`，
    其中 `p^{-x}` 写成 `exp(-x log p)`。 -/
noncomputable def localGram (p : ℕ) (φ ψ : ℝ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, localWeight p x * (φ x * star (ψ x))

/-- 局部内积的共轭对称：`star ⟨ψ, φ⟩_p = ⟨φ, ψ⟩_p`。 -/
theorem localGram_star (p : ℕ) (φ ψ : ℝ → ℂ) :
    star (localGram p ψ φ) = localGram p φ ψ := by
  rw [localGram, localGram, ← intervalIntegral_star]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [star_mul, star_mul, star_star, localWeight_star]
  ring

/-! ### 三、素数侧 Gram 矩阵（可算） -/

/-- **素数侧 Gram 矩阵**：`P_{jk} = Σ_{p ∈ primesBelow N} (log p) · ⟨φ_j, φ_k⟩_p`。
    这是 Weil 显式公式素数侧在有限截断 + 局部权口径下的显式实现。 -/
noncomputable def weilPrimeGram {n : Type} [Fintype n] [DecidableEq n]
    (N : ℕ) (φ : n → ℝ → ℂ) : Matrix n n ℂ :=
  fun j k => ∑ p ∈ Nat.primesBelow N, (Real.log (p : ℝ) : ℂ) * localGram p (φ j) (φ k)

/-- 素数侧 Gram 的点式展开（定义展开，便于下游 `simp`）。 -/
theorem weilPrimeGram_apply {n : Type} [Fintype n] [DecidableEq n]
    (N : ℕ) (φ : n → ℝ → ℂ) (j k : n) :
    weilPrimeGram N φ j k = ∑ p ∈ Nat.primesBelow N, (Real.log (p : ℝ) : ℂ) * localGram p (φ j) (φ k) :=
  rfl

/-- **素数侧厄米性（点式）**：`star P_{kj} = P_{jk}`。 -/
theorem weilPrimeGram_star_apply {n : Type} [Fintype n] [DecidableEq n]
    (N : ℕ) (φ : n → ℝ → ℂ) (j k : n) :
    star (weilPrimeGram N φ k j) = weilPrimeGram N φ j k := by
  rw [weilPrimeGram_apply, weilPrimeGram_apply, star_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [star_mul, localGram_star, ofReal_star]
  ring

/-- **素数侧厄米性（矩阵式）**：`Pᴴ = P`。 -/
theorem weilPrimeGram_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (N : ℕ) (φ : n → ℝ → ℂ) :
    (weilPrimeGram N φ)ᴴ = weilPrimeGram N φ := by
  ext j k
  rw [Matrix.conjTranspose_apply]
  exact weilPrimeGram_star_apply N φ j k

/-! ### 四、零点侧 `‖φ̂_j(ρ)‖²` 与解析上界 -/

/-- 测试函数的局部 Fourier 变换：`φ̂(ρ) = ∫₀¹ φ(x) e^{I ρ x} dx`。 -/
noncomputable def phiHat (φ : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, φ x * Complex.exp (Complex.I * ρ * x)

/-- `∫₀¹ ‖φ‖` 非负。 -/
theorem integral_norm_nonneg (φ : ℝ → ℂ) (hφ : Continuous φ) :
    0 ≤ ∫ x in (0 : ℝ)..1, ‖φ x‖ := by
  have h1 : IntervalIntegrable (fun x : ℝ => ‖φ x‖) volume 0 1 :=
    hφ.norm.intervalIntegrable (μ := volume) 0 1
  have h0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1 :=
    intervalIntegrable_const (μ := volume)
  simpa using intervalIntegral.integral_mono_on zero_le_one h0 h1 (fun x _ => norm_nonneg _)

/-- **`φ̂` 的 L¹ 上界**：`‖φ̂(ρ)‖ ≤ exp ‖ρ‖ · ∫₀¹ ‖φ‖`。
    相位 `e^{Iρx}` 在 `x ∈ [0,1]` 上的模是 `exp(-(ρx).im) ≤ exp ‖ρ‖`。 -/
theorem phiHat_norm_le (φ : ℝ → ℂ) (hφ : Continuous φ) (ρ : ℂ) :
    ‖phiHat φ ρ‖ ≤ Real.exp ‖ρ‖ * ∫ x in (0 : ℝ)..1, ‖φ x‖ := by
  calc ‖∫ x in (0 : ℝ)..1, φ x * Complex.exp (Complex.I * ρ * x)‖
      ≤ ∫ x in (0 : ℝ)..1, ‖φ x * Complex.exp (Complex.I * ρ * x)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ x in (0 : ℝ)..1, ‖φ x‖ * Real.exp ‖ρ‖ := by
        have hphase : Continuous (fun x : ℝ => Complex.exp (Complex.I * ρ * (x : ℂ))) :=
          Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
        have h1 : Continuous (fun x : ℝ => φ x * Complex.exp (Complex.I * ρ * (x : ℂ))) :=
          hφ.mul hphase
        have h2 : Continuous (fun x : ℝ => ‖φ x‖ * Real.exp ‖ρ‖) :=
          hφ.norm.mul (continuous_const : Continuous fun _ : ℝ => Real.exp ‖ρ‖)
        refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ ?_
        · exact h1.norm.intervalIntegrable (μ := volume) 0 1
        · exact h2.intervalIntegrable (μ := volume) 0 1
        · intro x hx
          obtain ⟨hx0, hx1⟩ := hx
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have hxnorm : ‖x‖ ≤ 1 := by
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith, by linarith⟩
          calc (Complex.I * ρ * (x : ℂ)).re ≤ ‖Complex.I * ρ * (x : ℂ)‖ := Complex.re_le_norm _
            _ = ‖ρ‖ * ‖(x : ℂ)‖ := by rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
            _ = ‖ρ‖ * ‖x‖ := by rw [Complex.norm_real]
            _ ≤ ‖ρ‖ * 1 := by gcongr
            _ = ‖ρ‖ := by ring
    _ = Real.exp ‖ρ‖ * ∫ x in (0 : ℝ)..1, ‖φ x‖ := by
        rw [intervalIntegral.integral_mul_const]
        ring

/-- 带零点高度界 `‖ρ‖ ≤ T` 的版本。 -/
theorem phiHat_norm_le_exp (φ : ℝ → ℂ) (hφ : Continuous φ) {ρ : ℂ} {T : ℝ}
    (hT : ‖ρ‖ ≤ T) :
    ‖phiHat φ ρ‖ ≤ Real.exp T * ∫ x in (0 : ℝ)..1, ‖φ x‖ := by
  have h := phiHat_norm_le φ hφ ρ
  have hle : Real.exp ‖ρ‖ ≤ Real.exp T := Real.exp_le_exp.mpr hT
  have hI := integral_norm_nonneg φ hφ
  exact h.trans (mul_le_mul_of_nonneg_right hle hI)

/-- **`‖φ̂‖²` 的解析上界**：`‖φ̂(ρ)‖² ≤ (exp T)² · (∫₀¹ ‖φ‖)²`，`‖ρ‖ ≤ T`。 -/
theorem phiHat_sq_le (φ : ℝ → ℂ) (hφ : Continuous φ) {ρ : ℂ} {T : ℝ}
    (hT : ‖ρ‖ ≤ T) :
    ‖phiHat φ ρ‖ ^ 2 ≤ (Real.exp T) ^ 2 * (∫ x in (0 : ℝ)..1, ‖φ x‖) ^ 2 := by
  have h := phiHat_norm_le_exp φ hφ hT
  have hI := integral_norm_nonneg φ hφ
  have hB : 0 ≤ Real.exp T * ∫ x in (0 : ℝ)..1, ‖φ x‖ :=
    mul_nonneg (Real.exp_pos T).le hI
  calc ‖phiHat φ ρ‖ ^ 2
      ≤ (Real.exp T * ∫ x in (0 : ℝ)..1, ‖φ x‖) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (phiHat φ ρ)]) h
    _ = (Real.exp T) ^ 2 * (∫ x in (0 : ℝ)..1, ‖φ x‖) ^ 2 := by ring

/-! ### 五、零点侧对角 Gram：`hz` 从自由变量变成对象 -/

/-- **零点侧对角**：`hz_j = Σ_{ρ ∈ S} ‖φ̂_j(ρ)‖²`（实值，以 `ℂ` 类型给出）。 -/
noncomputable def weilZeroDiag {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset ℂ) (φ : n → ℝ → ℂ) : n → ℂ :=
  fun j => ((∑ ρ ∈ S, ‖phiHat (φ j) ρ‖ ^ 2 : ℝ) : ℂ)

/-- 零点侧对角的实值性：`star hz_j = hz_j`（签名才有意义）。 -/
theorem weilZeroDiag_star {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset ℂ) (φ : n → ℝ → ℂ) (j : n) :
    star (weilZeroDiag S φ j) = weilZeroDiag S φ j := by
  rw [weilZeroDiag]
  simp

/-- **`hz_j` 的解析上界**：零点集 `S` 全在 `‖ρ‖ ≤ T` 内时
    `hz_j ≤ card S · (exp T)² · (∫₀¹ ‖φ_j‖)²`。 -/
theorem weilZeroDiag_re_le {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset ℂ) (φ : n → ℝ → ℂ) (hφ : ∀ j, Continuous (φ j)) (T : ℝ)
    (hS : ∀ ρ ∈ S, ‖ρ‖ ≤ T) (j : n) :
    (weilZeroDiag S φ j).re
      ≤ (S.card : ℝ) * ((Real.exp T) ^ 2 * (∫ x in (0 : ℝ)..1, ‖φ j x‖) ^ 2) := by
  rw [weilZeroDiag, Complex.ofReal_re]
  calc ∑ ρ ∈ S, ‖phiHat (φ j) ρ‖ ^ 2
      ≤ ∑ _ρ ∈ S, (Real.exp T) ^ 2 * (∫ x in (0 : ℝ)..1, ‖φ j x‖) ^ 2 :=
        Finset.sum_le_sum (fun ρ hρ => phiHat_sq_le (φ j) (hφ j) (hS ρ hρ))
    _ = S.card • ((Real.exp T) ^ 2 * (∫ x in (0 : ℝ)..1, ‖φ j x‖) ^ 2) :=
        Finset.sum_const _
    _ = (S.card : ℝ) * ((Real.exp T) ^ 2 * (∫ x in (0 : ℝ)..1, ‖φ j x‖) ^ 2) := by
        rw [nsmul_eq_mul]

/-! ### 六、把 A 真正组装出来 -/

/-- **可算的 Weil Gram 矩阵**：`A = diag(hz) − P`，两个入参现在都是对象而非自由变量。 -/
noncomputable def weilGramConcrete {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset ℂ) (N : ℕ) (φ : n → ℝ → ℂ) : Matrix n n ℂ :=
  weilGramMatrix (weilZeroDiag S φ) (weilPrimeGram N φ)

/-- **A 厄米**：可算版本仍满足 `Aᴴ = A`。 -/
theorem weilGramConcrete_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset ℂ) (N : ℕ) (φ : n → ℝ → ℂ) :
    (weilGramConcrete S N φ)ᴴ = weilGramConcrete S N φ :=
  weilGram_conjTranspose (weilZeroDiag S φ) (weilPrimeGram N φ)
    (weilZeroDiag_star S φ) (weilPrimeGram_star_apply N φ)

/-- **A 的二次型**：可算版本上 `hneg` 作用的就是这个量。 -/
theorem weilGramConcrete_quadratic {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset ℂ) (N : ℕ) (φ : n → ℝ → ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (weilGramConcrete S N φ *ᵥ x) =
      (∑ j, weilZeroDiag S φ j * (star (x j) * x j))
        - star x ⬝ᵥ (weilPrimeGram N φ *ᵥ x) :=
  weilGram_quadratic (weilZeroDiag S φ) (weilPrimeGram N φ) x

/-- **惯性律落到可算 A 上**：若截断矩阵 A 有签名 `(p, q)`，
    则任何使 A 二次型实部 `≤ 0` 的单射子空间维数不超过 `q`。
    签名本身仍是假设（`hSig`），本文件不声称知道 A 的签名。 -/
theorem weilGramConcrete_negativeDim_le {n k : Type} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (S : Finset ℂ) (N : ℕ) (φ : n → ℝ → ℂ) {p q : ℕ}
    (hSig : ADefiniteSignature (weilGramConcrete S N φ) p q) (B : Matrix n k ℂ)
    (hB : Function.Injective B.mulVec)
    (hneg : ∀ v : k → ℂ,
      (star (B *ᵥ v) ⬝ᵥ (weilGramConcrete S N φ *ᵥ (B *ᵥ v))).re ≤ 0) :
    Fintype.card k ≤ q :=
  weilGram_negativeDim_le (weilZeroDiag S φ) (weilPrimeGram N φ) hSig B hB hneg

end RHSpectralDuality

#print axioms RHSpectralDuality.intervalIntegral_star
#print axioms RHSpectralDuality.localGram_star
#print axioms RHSpectralDuality.weilPrimeGram_star_apply
#print axioms RHSpectralDuality.weilPrimeGram_conjTranspose
#print axioms RHSpectralDuality.integral_norm_nonneg
#print axioms RHSpectralDuality.phiHat_norm_le
#print axioms RHSpectralDuality.phiHat_norm_le_exp
#print axioms RHSpectralDuality.phiHat_sq_le
#print axioms RHSpectralDuality.weilZeroDiag_star
#print axioms RHSpectralDuality.weilZeroDiag_re_le
#print axioms RHSpectralDuality.weilGramConcrete_conjTranspose
#print axioms RHSpectralDuality.weilGramConcrete_quadratic
#print axioms RHSpectralDuality.weilGramConcrete_negativeDim_le
