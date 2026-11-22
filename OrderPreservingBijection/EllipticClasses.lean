/-
  椭圆共轭类矩阵层：把原先 `opaque ellipticClassLengths` + `by sorry` 的有限性
  换成具体定义 + 定理。这是 E 链（ellipticClassLengths → ellipticTerm →
  MollifiedTestFunction）的源头修复，目的只有一个：让 `#print axioms` 不再吐出
  匿名 `sorryAx`。

  这一层的逻辑链（全部可核验）：
    ① 椭圆 ⟺ 迹的域迹绝对值 < 2（模型约定，见 QuadraticFieldFive 的迹值分类）；
    ② 该条件经 `GoldenInt.fieldTrace_mem_of_abs_lt_two` 推出迹的域迹 ∈ {−1,0,1}；
    ③ 迹决定旋转角：SU(2) 中 tr = 2cos θ ⟹ θ = arccos(tr/2)，与共轭类无关
       —— 只需「长度是迹的函数」，不需要「迹分类共轭类」这套 Θ/特征标表；
    ④ 故特征长度集合 ⊆ {arccos(−1/2), arccos 0, arccos(1/2)}，有限。

  留在 prose 里的约定（未形式化、也不再以公理形式存在）：
    · 迹的读法：本模型取域迹 `fieldTrace z = 2a + b`（而非实嵌入值 a + bφ）；
    · 上链 ③ 中的归一化（tr = 2cos θ 而非 2cos(θ/2)），只影响长度数值，不影响有限性。
  若要把这两条变成定理，需要真建 PSL₂/四元数代数矩阵群层 + 特征标表，属另一支线。
-/

import OrderPreservingBijection.QuadraticFieldFive
import Mathlib.Data.Matrix.Basic

namespace OrderPreservingBijection

open GoldenInt

/- ======================================================================== -/
-- 第1节：O_K 上的 2×2 矩阵层
/- ======================================================================== -/

/-- 2×2 矩阵层：O_K = ℤ[φ] 上的矩阵（PSL₂(O_K) 的元素，当前不商 ±I）。 -/
abbrev GoldenMatrix : Type := Matrix (Fin 2) (Fin 2) GoldenInt

/-- 矩阵迹 tr(M) = M₀₀ + M₁₁ ∈ O_K。 -/
def matrixTrace (M : GoldenMatrix) : GoldenInt := M 0 0 + M 1 1

/-- 矩阵行列式 det(M) = M₀₀M₁₁ − M₀₁M₁₀ ∈ O_K。 -/
def matrixDet (M : GoldenMatrix) : GoldenInt := M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- 椭圆判据（模型约定）：迹的域迹绝对值 < 2。
    实椭圆元素（旋转角 θ ∉ {0, π}）满足此条件；模型取域迹作为迹的读数。 -/
def IsEllipticMatrix (M : GoldenMatrix) : Prop :=
  |((GoldenInt.fieldTrace (matrixTrace M) : ℝ))| < 2

/- ======================================================================== -/
-- 第2节：迹 → 特征长度 → 有限集合
/- ======================================================================== -/

/-- 椭圆迹候选值：{−1, 0, 1}。 -/
def ellipticTraces : Finset ℤ := {(-1 : ℤ), 0, 1}

/-- 迹 → 特征长度：SU(2) 中 tr = 2cos θ，故 θ = arccos(tr/2)，长度取 arccos。 -/
noncomputable def ellipticLengthOfTrace (t : ℤ) : ℝ :=
  Real.arccos ((t : ℝ) / 2)

/-- 椭圆共轭类特征长度集合（具体定义，替换原 `opaque`）：
    E_ell = { ℓ(t) : t ∈ {−1,0,1} }。 -/
noncomputable def ellipticClassLengths : Set ℝ := by
  classical
  exact ((ellipticTraces.image ellipticLengthOfTrace : Finset ℝ) : Set ℝ)

/-- 椭圆类特征长度集合有限（**定理**，替换原 `by sorry`）。
    证明：它是三元素有限集的像。 -/
theorem ellipticClassLengths_finite : Set.Finite ellipticClassLengths := by
  classical
  unfold ellipticClassLengths
  exact Set.Finite.ofFinset (ellipticTraces.image ellipticLengthOfTrace) (by simp)

/-- 矩阵层的桥：任意椭圆矩阵 M，其迹（经域迹）对应的特征长度落在 `ellipticClassLengths`。
    这条把「具体的长度集合」与「代数半 `fieldTrace_mem_of_abs_lt_two`」扣在一起，
    使 ①②③④ 四步在 kernel 里闭合。 -/
theorem elliptic_length_mem_of_matrix (M : GoldenMatrix) (h : IsEllipticMatrix M) :
    ellipticLengthOfTrace (GoldenInt.fieldTrace (matrixTrace M)) ∈ ellipticClassLengths := by
  classical
  unfold ellipticClassLengths
  rcases GoldenInt.fieldTrace_mem_of_abs_lt_two (matrixTrace M) h with h1 | h2 | h3
  · rw [h1]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (by simp [ellipticTraces]))
  · rw [h2]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (by simp [ellipticTraces]))
  · rw [h3]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (by simp [ellipticTraces]))

end OrderPreservingBijection
