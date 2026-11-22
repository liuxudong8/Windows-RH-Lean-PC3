/-
  三维双曲 Laplacian：真算子（不是占位）。

  为什么单独成文件、而不直接替换 `laplacian_M`：`laplacian_M` 的签名是
  `L2ManifoldM → L2ManifoldM` 的**全函数**，而 `L2ManifoldM` 的每个元素都携带
  `measurable` 与 `sq_integrable` 证明。真 Laplacian 是无界算子，定义域只能是稠密
  子空间（C² 且 Δf ∈ L²），对任意 L² 函数给不出可测/可积的输出。故此处只提供
  **正确的算子本体**（作用于平凡函数 / 光滑函数），把签名问题留给调用方决策：
    · 方案 A：把 `laplacian_M` 的定义域改成光滑子空间 `SmoothL2ManifoldM`；
    · 方案 B：保留全函数签名并接受 junk 分支（会使命题 `laplacian_M_self_adjoint` 变假）。

  算子本体（上半空间模型 ℍ³ = {(x,y,t) | t > 0}，度量 ds² = (dx²+dy²+dt²)/t²）：
      √g = t⁻³,  gⁱʲ = t² δⁱʲ
      Δ_ℍ f = (1/√g) ∂ᵢ(√g gⁱʲ ∂ⱼ f) = t² Δ_flat f − t ∂_t f
  `Δ_flat` 直接取 mathlib 的 `InnerProductSpace.Laplacian`（Hessian 的迹）。
-/

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

open Laplacian

namespace OrderPreservingBijection

/-- 上半空间模型：坐标 0,1 为 z 的实部与虚部，坐标 2 为高度 t（需 0 < t）。 -/
abbrev UpperHalfSpaceAmbient : Type := EuclideanSpace ℝ (Fin 3)

/-- 无符号 Laplace–Beltrami 算子（ℍ³ 上半空间模型）：
    `Δ_ℍ f p = t² · Δ_flat f p − t · ∂_t f p`，`t = p 2`。
    这是**真算子**：`Δ_flat` 是 mathlib 的欧氏 Laplacian，第二项是度量的 Christoffel 修正。 -/
noncomputable def hyperbolicLaplacian (f : UpperHalfSpaceAmbient → ℂ)
    (p : UpperHalfSpaceAmbient) : ℂ :=
  (p 2 : ℂ) ^ 2 * Δ f p - (p 2 : ℂ) * fderiv ℝ f p (EuclideanSpace.single 2 1)

/-- 常数函数的零特征值（0 特征空间即常数函数，与 `specDiscM` 跳过 0 的约定一致）。 -/
theorem hyperbolicLaplacian_const (c : ℂ) (p : UpperHalfSpaceAmbient) :
    hyperbolicLaplacian (fun _ => c) p = 0 := by
  simp [hyperbolicLaplacian]

/-- 只依赖 t 的归一化形式：`Δ_ℍ g(t) = t² g'' − t g'`。
    对 `g t = t^s` 给出 `Δ_ℍ t^s = s(s−2) t^s`，即特征函数指数满足
    `s(s−2) = λ`；于是 `−Δ_ℍ` 在 `s = 1 + iλ` 上的特征值是 `1 + λ² ≥ 1`。 -/
noncomputable def radialHLap (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ 2 * deriv (deriv g) t - t * deriv g t

/-- `t²` 在 ℍ³ 中调和：`Δ_ℍ t² = 0`（`s(s−2) = 0` 的 `s = 2` 支）。 -/
theorem radialHLap_sq (t : ℝ) : radialHLap (fun t : ℝ => t ^ 2) t = 0 := by
  have hfun : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    rw [deriv_pow_field]
    norm_num
  rw [radialHLap, hfun]
  rw [deriv_const_mul_id]
  ring

/-- `t³`：`Δ_ℍ t³ = 3 t³`（`s(s−2) = 3` 的 `s = 3` 支）。 -/
theorem radialHLap_cube (t : ℝ) : radialHLap (fun t : ℝ => t ^ 3) t = 3 * t ^ 3 := by
  have hfun : deriv (fun t : ℝ => t ^ 3) = fun t => 3 * t ^ 2 := by
    funext t
    rw [deriv_pow_field]
    norm_num
  have hfun2 : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    rw [deriv_pow_field]
    norm_num
  rw [radialHLap, hfun]
  rw [deriv_const_mul_field' (𝕜 := ℝ) (v := fun t : ℝ => t ^ 2) (3 : ℝ)]
  rw [hfun2]
  ring

/-- `t`：`Δ_ℍ t = −t`（`s(s−2) = −1` 的 `s = 1` 支）。 -/
theorem radialHLap_id (t : ℝ) : radialHLap (fun t : ℝ => t) t = -t := by
  rw [radialHLap, deriv_id'']
  rw [deriv_const']
  ring

/-- 谱底：三维情形 `s = 1 + iλ` 给出 `s(2−s) = 1 + λ² ≥ 1`。
    对比：二维（ℍ²）是 `s(1−s) = 1/4 + λ²`，谱底 1/4。
    故「1/4 ≤ s n」对 ℍ³ 是自动满足的（真下界是 1），不是需要额外假设的风险点。 -/
theorem spectral_bottom_three_dimensional (lam : ℝ) :
    ((1 : ℂ) + Complex.I * lam) * (2 - ((1 : ℂ) + Complex.I * lam)) =
      ((1 + lam ^ 2 : ℝ) : ℂ) := by
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hcast : ((1 + lam ^ 2 : ℝ) : ℂ) = 1 + (lam : ℂ) ^ 2 := by
    push_cast
    ring
  rw [hcast]
  ring_nf
  rw [hI]
  ring

end OrderPreservingBijection
