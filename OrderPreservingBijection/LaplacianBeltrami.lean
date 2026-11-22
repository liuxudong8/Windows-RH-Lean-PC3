/-
LaplacianBeltrami.lean
方案 A1：把 stage_4 / HeatKernel 里的占位 `laplacian_M`（原为
`fun _ => Classical.arbitrary L2ManifoldM`）换成真正的 Laplace–Beltrami 算子。

设计要点
--------
1. 定义域收窄：`SmoothL2ManifoldM` = 「L² 且在 ℍ³ 上 C²、且 Δ_ℍ f 仍平方可积」的函数，
   把三项义务（`contDiffOn` / 可测 / 平方可积）作为结构字段随函数一起携带。
2. 算子取值由坐标公式给出
     Δ_ℍ f = t² (f_xx + f_yy + f_tt) − t · f_t,
   与 `HyperbolicLaplacian.lean` 的 `hyperbolicLaplacian`（EuclideanSpace ℝ (Fin 3) 载体）
   是同一公式的两种载体。此处取「坐标原生」载体：`ℂ × ℝ` 没有 ℝ-内积实例
   （`ProdL2` 的实例不覆盖 `ℂ × ℝ`），所以不去调 flat `Δ`，而是直接按标准正交基
   取二阶导数的迹：`(1,0)`、`(I,0)`、`(0,1)` 在 ℝ 上正交归一，故坐标迹 = 迹。
3. 因为定义域与陪域都由结构给出，`laplacian_M` 在光滑域上是**全函数**，
   域外根本没有输入点，因此不存在 `Classical.arbitrary` 那种 junk 值。
4. 二阶导数一律用 `iteratedFDerivWithin`（限制在半空间 `halfSpaceSet`），
   这与 `ContDiffOn` 的假设同一层次，避免要求函数跨 `t = 0` 光滑。
-/

import OrderPreservingBijection.ManifoldInfrastructure
import OrderPreservingBijection.HyperbolicLaplacian

open MeasureTheory MeasureTheory.Measure

namespace OrderPreservingBijection

/-- 上半空间作为 `ℂ × ℝ` 的开子集（`t > 0`）。 -/
def halfSpaceSet : Set (ℂ × ℝ) := {p | 0 < p.2}

/-- 把定义在 `ℍ³`（子类型）上的函数提升为 `ℂ × ℝ` 上的函数，区域外取 0。
    这样 `fderivWithin`/`iteratedFDerivWithin` 可以在母空间里对 `p.val` 取局部导数。 -/
noncomputable def hypLift (f : ManifoldM → ℂ) : ℂ × ℝ → ℂ :=
  fun p => if h : 0 < p.2 then f ⟨p, h⟩ else 0

/-- 坐标基向量 x 轴（对应 Re z）。 -/
def eX : ℂ × ℝ := (1, 0)

/-- 坐标基向量 y 轴（对应 Im z）。 -/
def eY : ℂ × ℝ := (Complex.I, 0)

/-- 坐标基向量 t 轴（对应高度）。 -/
def eT : ℂ × ℝ := (0, 1)

/-- 平坦 Laplacian（坐标迹）：在 `halfSpaceSet` 内对三个坐标方向取二阶导数之和。
    `{1, I, (0,1)}` 是 `ℂ × ℝ` 的标准正交基（ℝ-意义下），故坐标迹 = 平坦迹。 -/
noncomputable def flatLapWithin (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  iteratedFDerivWithin ℝ 2 f halfSpaceSet p ![eX, eX]
    + iteratedFDerivWithin ℝ 2 f halfSpaceSet p ![eY, eY]
    + iteratedFDerivWithin ℝ 2 f halfSpaceSet p ![eT, eT]

/-- 双曲 Laplace–Beltrami 算子：Δ_ℍ f = t² (f_xx + f_yy + f_tt) − t · f_t。
    这是 `HyperbolicLaplacian.lean` 中 `hyperbolicLaplacian`
    `(p 2)^2 * Δ f p − (p 2) * fderiv ℝ f p (single 2 1)` 的坐标载体版本。 -/
noncomputable def hyperbolicLapOn (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  (p.2 : ℂ) ^ 2 * flatLapWithin f p - (p.2 : ℂ) * fderivWithin ℝ f halfSpaceSet p eT

/-- 光滑 L² 域：`laplacian_M` 的合法输入。
    携带三项义务，使陪域 `L2ManifoldM` 能被无 junk 地构造：
    * `contDiffOn`：在半空间内 C²（Δ_ℍ 有意义）；
    * `lap_measurable`：Δ_ℍ f 作为 `ℍ³` 上的函数可测；
    * `lap_sq_integrable`：Δ_ℍ f 平方可积（落在 L²）。 -/
structure SmoothL2ManifoldM where
  /-- 底层的 L² 函数 -/
  toL2 : L2ManifoldM
  /-- 在半空间内 C² -/
  contDiffOn : ContDiffOn ℝ 2 (hypLift toL2.toFun) halfSpaceSet
  /-- Δ_ℍ f 可测 -/
  lap_measurable : Measurable (fun p : ManifoldM => hyperbolicLapOn (hypLift toL2.toFun) p.val)
  /-- Δ_ℍ f 平方可积 -/
  lap_sq_integrable :
    Integrable (fun p : ManifoldM => ‖hyperbolicLapOn (hypLift toL2.toFun) p.val‖ ^ 2) hyperbolicMeasure3

/-- 强制转换：光滑域的元可以直接当 `L2ManifoldM` 用（内积、范数等）。 -/
instance : Coe SmoothL2ManifoldM L2ManifoldM := ⟨fun f => f.toL2⟩

/-- 真正的三维 Laplace–Beltrami 算子。
    与旧占位 `fun _ => Classical.arbitrary L2ManifoldM` 的差别：
    这里是**由公式算出来的**函数值，每个输入 `f` 的输出逐点等于
    `t²(f_xx+f_yy+f_tt) − t f_t`；不存在「对本该算不出的输入随便给一个 L² 元」。 -/
noncomputable def laplacian_M (f : SmoothL2ManifoldM) : L2ManifoldM :=
  { toFun := fun p => hyperbolicLapOn (hypLift f.toL2.toFun) p.val
    measurable := f.lap_measurable
    sq_integrable := f.lap_sq_integrable }

/-- 提升后的零函数仍是零函数（用于构造 `Zero` 实例）。 -/
theorem hypLift_zero : hypLift (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext p
  by_cases h : 0 < p.2
  · simp [hypLift, h]
  · simp [hypLift, h]

/-- 光滑域上的零元素：Δ_ℍ 0 = 0，故三项义务都成立。 -/
noncomputable def smoothZero : SmoothL2ManifoldM where
  toL2 := (0 : L2ManifoldM)
  contDiffOn := by
    have h : (0 : L2ManifoldM).toFun = fun _ => (0 : ℂ) := rfl
    rw [h, hypLift_zero]
    exact contDiffOn_const
  lap_measurable := by
    have h : (0 : L2ManifoldM).toFun = fun _ => (0 : ℂ) := rfl
    rw [h, hypLift_zero]
    simp [hyperbolicLapOn, flatLapWithin]
  lap_sq_integrable := by
    have h : (0 : L2ManifoldM).toFun = fun _ => (0 : ℂ) := rfl
    rw [h, hypLift_zero]
    simp [hyperbolicLapOn, flatLapWithin]

/-- 光滑域是带零元素的类型。 -/
noncomputable instance instZeroSmoothL2ManifoldM : Zero SmoothL2ManifoldM := ⟨smoothZero⟩

/-- 光滑域的外延性：三项义务都是命题，故 `toL2` 相等即结构元相等（证明不可分辨）。
    下游要在 `laplacian_M` 的参数位置做改写时用这条。 -/
theorem SmoothL2ManifoldM.ext {f g : SmoothL2ManifoldM} (h : f.toL2 = g.toL2) : f = g := by
  cases f
  cases g
  simp_all

/-- 逐点展开引理：`laplacian_M f p = t²(f_xx+f_yy+f_tt) − t f_t`。
    这条引理把「算子」和「坐标公式」钉在一起，方便下游做分部积分。
    注意：因为 `L2Function` 是结构，`laplacian_M f p` 展开为
    `(laplacian_M f).toFun p`，这里给出显式的等式版本。 -/
theorem laplacian_M_apply (f : SmoothL2ManifoldM) (p : ManifoldM) :
    (laplacian_M f).toFun p = hyperbolicLapOn (hypLift f.toL2.toFun) p.val := rfl

end OrderPreservingBijection
