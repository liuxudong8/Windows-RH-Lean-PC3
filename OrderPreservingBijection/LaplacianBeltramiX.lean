/-
LaplacianBeltramiX.lean
二维版 A1：把 `stage_4` 里的占位 `laplacian_X`（原为
`fun _ => Classical.arbitrary L2ManifoldX`）换成真正的 Laplace–Beltrami 算子。

与三维版（`LaplacianBeltrami.lean`）的差别只在一个地方：几何因子。
* ℍ³：`√g = 1/t³`，`Δ_ℍ f = t² · Δ_flat f − t · f_t`（有一阶项）
* ℍ²：`√g = 1/y²`，`Δ_ℍ f = y² · Δ_flat f`（**无一阶项**）

这里 `Δ_flat` 仍按坐标取二阶迹：`ℂ` 上的标准正交基是 `1`（x 轴）与 `I`（y 轴），
故 `Δ_flat f = f_xx + f_yy = Σ_k iteratedFDerivWithin ℝ 2 f s z ![e_k, e_k]`。

定义域收窄为 `SmoothL2ManifoldX`（C² 且 Δ_ℍ f 平方可积），域外无输入点，
因此不存在 junk 值——与三维同一策略（方案 A1）。
-/

import OrderPreservingBijection.ManifoldInfrastructure
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

open MeasureTheory MeasureTheory.Measure

namespace OrderPreservingBijection

/-- 上半平面作为 `ℂ` 的开子集（`0 < Im z`）。 -/
def upperHalfPlaneSet : Set ℂ := {z | 0 < z.im}

/-- 把定义在 `ℍ²`（子类型）上的函数提升为 `ℂ` 上的函数，区域外取 0。 -/
noncomputable def planeLift (f : ManifoldX → ℂ) : ℂ → ℂ :=
  fun z => if h : 0 < z.im then f ⟨z, h⟩ else 0

/-- 坐标基：x 轴（`1`）。 -/
def exC : ℂ := 1

/-- 坐标基：y 轴（`I`）。`1` 与 `I` 在 ℝ 上正交归一。 -/
def eyC : ℂ := Complex.I

/-- 平坦 Laplacian（坐标迹）：`f_xx + f_yy`，在 `upperHalfPlaneSet` 内取二阶导数。 -/
noncomputable def flatLapPlane (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedFDerivWithin ℝ 2 f upperHalfPlaneSet z ![exC, exC]
    + iteratedFDerivWithin ℝ 2 f upperHalfPlaneSet z ![eyC, eyC]

/-- 二维双曲 Laplace–Beltrami 算子：`Δ_ℍ f = y² (f_xx + f_yy)`。
    与 `HyperbolicLaplacian.lean` 的 ℍ³ 版
    `(p 2)^2 * Δ f p − (p 2) * fderiv ℝ f p (single 2 1)` 对照：
    二维没有 `− y f_y` 这一项，因为 `√g = 1/y²` 的导数项与 `g^{yy}` 相消。 -/
noncomputable def hyperbolicLapPlane (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z.im : ℂ) ^ 2 * flatLapPlane f z

/-- 光滑 L² 域（二维）：`laplacian_X` 的合法输入。
    携带三项义务，使陪域 `L2ManifoldX` 能被无 junk 地构造。 -/
structure SmoothL2ManifoldX where
  /-- 底层的 L² 函数 -/
  toL2 : L2ManifoldX
  /-- 在上半平面内 C² -/
  contDiffOn : ContDiffOn ℝ 2 (planeLift toL2.toFun) upperHalfPlaneSet
  /-- Δ_ℍ f 可测 -/
  lap_measurable : Measurable (fun z : ManifoldX => hyperbolicLapPlane (planeLift toL2.toFun) z.val)
  /-- Δ_ℍ f 平方可积 -/
  lap_sq_integrable :
    Integrable (fun z : ManifoldX => ‖hyperbolicLapPlane (planeLift toL2.toFun) z.val‖ ^ 2) hyperbolicMeasure2

/-- 强制转换：光滑域的元可以直接当 `L2ManifoldX` 用。 -/
instance : Coe SmoothL2ManifoldX L2ManifoldX := ⟨fun f => f.toL2⟩

/-- 真正的二维 Laplace–Beltrami 算子（由公式算出，无 junk 分支）。 -/
noncomputable def laplacian_X (f : SmoothL2ManifoldX) : L2ManifoldX :=
  { toFun := fun z => hyperbolicLapPlane (planeLift f.toL2.toFun) z.val
    measurable := f.lap_measurable
    sq_integrable := f.lap_sq_integrable }

/-- 光滑域的外延性：`toL2` 相等即结构元相等（三项义务都是命题）。 -/
theorem SmoothL2ManifoldX.ext {f g : SmoothL2ManifoldX} (h : f.toL2 = g.toL2) : f = g := by
  cases f
  cases g
  simp_all

/-- 逐点展开引理：`laplacian_X f z = y²(f_xx + f_yy)`。 -/
theorem laplacian_X_apply (f : SmoothL2ManifoldX) (z : ManifoldX) :
    (laplacian_X f).toFun z = hyperbolicLapPlane (planeLift f.toL2.toFun) z.val := rfl

/-- 提升后的零函数仍是零函数。 -/
theorem planeLift_zero : planeLift (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext z
  by_cases h : 0 < z.im
  · simp [planeLift, h]
  · simp [planeLift, h]

/-- 光滑域上的零元素：Δ_ℍ 0 = 0。 -/
noncomputable def smoothZeroX : SmoothL2ManifoldX where
  toL2 := (0 : L2ManifoldX)
  contDiffOn := by
    have h : (0 : L2ManifoldX).toFun = fun _ => (0 : ℂ) := rfl
    rw [h, planeLift_zero]
    exact contDiffOn_const
  lap_measurable := by
    have h : (0 : L2ManifoldX).toFun = fun _ => (0 : ℂ) := rfl
    rw [h, planeLift_zero]
    simp [hyperbolicLapPlane, flatLapPlane]
  lap_sq_integrable := by
    have h : (0 : L2ManifoldX).toFun = fun _ => (0 : ℂ) := rfl
    rw [h, planeLift_zero]
    simp [hyperbolicLapPlane, flatLapPlane]

/-- 光滑域是带零元素的类型。 -/
noncomputable instance instZeroSmoothL2ManifoldX : Zero SmoothL2ManifoldX := ⟨smoothZeroX⟩

/-- 常数函数的双曲 Laplacian 为零（自检：公式在常数上不产生伪项）。
    这条同时验证了 `iteratedFDerivWithin` 对常数的迹为零（`iteratedFDerivWithin_const_of_ne`），
    且 `y²` 因子不引入残留。 -/
theorem hyperbolicLapPlane_const (c : ℂ) : hyperbolicLapPlane (fun _ => c) = fun _ => (0 : ℂ) := by
  have h0 : iteratedFDerivWithin ℝ 2 (fun _ : ℂ => c) upperHalfPlaneSet = 0 :=
    iteratedFDerivWithin_const_of_ne (𝕜 := ℝ) (n := 2) (by norm_num) c upperHalfPlaneSet
  funext z
  simp [hyperbolicLapPlane, flatLapPlane, h0]

/-- Casimir 恒等式（ℍ²）：`s = 1/2 + it` 时 `s(1−s) = 1/4 + t²`。
    这是 `maass_laplacian_has_discrete_spectrum` 里「特征值 = 1/4 + t_n²」的算术来源，
    与三维版 `s(2−s) = 1 + λ²` 对照。 -/
theorem casimir_two_dimensional (t : ℝ) :
    ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) * ((1 : ℂ) - ((1 / 2 : ℂ) + Complex.I * (t : ℂ)))
      = (1 / 4 : ℂ) + (t : ℂ) ^ 2 := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  calc ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) * ((1 : ℂ) - ((1 / 2 : ℂ) + Complex.I * (t : ℂ)))
      = ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) * ((1 / 2 : ℂ) - Complex.I * (t : ℂ)) := by ring
    _ = (1 / 4 : ℂ) - Complex.I ^ 2 * (t : ℂ) ^ 2 := by ring
    _ = (1 / 4 : ℂ) + (t : ℂ) ^ 2 := by rw [hI]; ring

end OrderPreservingBijection
