/-
SylvesterInertia.lean
从归档侧 `RH_14` 搬运：`Development/AbelianVarietyTheory/Proofs/TwistedOperators/
HasSignatureFstUniqueSylvester.lean`（原作者 `GlobalTheory.SylvesterInertia`）。

来源与可复用性说明（对接条目 ②）：
* 归档侧该文件只依赖 `Mathlib` + 三个本地定义（`cT` / `Jpq` / `HasSignature`），
  证明 101 行**全为真证明，无 sorry**，用 finrank + 子空间交（`U ⊓ N ≠ ⊥`）论证
  正定子空间与负半定子空间不可能"多出来的那一维"同时容纳一个向量。
* 我们的 mathlib 是 `f8d25bb`（v4.34.0-rc2），归档侧是 `0df444a`（v4.33.1），
  故不是 import 而是重写；定义与证明主体保持原样，仅在命名空间与少量 API 上适配。
* 结论直接可用于我们这一侧：给「Weil 二次型 / A 矩阵的符号差（惯性指数）」
  下定义并证明良定义（`hasSignature_unique`），从而「谱对偶的符号差」不是
  依赖选取的量，而是矩阵的不变量。
-/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Exact.Sequence
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Order

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module
open scoped ComplexOrder

namespace OrderPreservingBijection.SylvesterInertia

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### 三个依赖定义（照抄归档侧，命名空间本地化） -/

/-- 矩阵的共轭转置（对合 `σ` 作用后转置）。`σ = starRingEnd ℂ` 时即 `Mᴴ`。 -/
def cT {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A :=
  (M.map σ)ᵀ

/-- 标准签名矩阵：`diag(1_p, −1_q)`（`p` 个 `+1`、`q` 个 `−1`）。 -/
def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

/-- `J` 具有签名 `(p, q)`：存在重排 `e` 与可逆 `P`，使
    `Pᴴ · J.reindex e e · P = Jpq p q`。这就是 Sylvester 惯性律里的"惯性指数"。 -/
def HasSignature (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

/-- 二次型取值 `xᴴ J x`。 -/
def qf (J : Matrix n n ℂ) (x : n → ℂ) : ℂ := star x ⬝ᵥ J *ᵥ x

/-! ### 搬运的辅助构造 -/

def inlMap (a b : ℕ) : (Fin a → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim z 0
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp

def inrMap (a b : ℕ) : (Fin b → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim 0 z
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp

lemma inlMap_injective (a b : ℕ) : Function.Injective (inlMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inl i)

lemma inrMap_injective (a b : ℕ) : Function.Injective (inrMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inr i)

def chg {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    (Fin a ⊕ Fin b → ℂ) →ₗ[ℂ] (n → ℂ) :=
  LinearMap.funLeft ℂ ℂ e ∘ₗ (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ).mulVecLin

lemma chg_apply {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ)
    (y : Fin a ⊕ Fin b → ℂ) :
    chg e P y = ((P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y) ∘ e := rfl

lemma chg_injective {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    Function.Injective (chg e P) := by
  intro y y' h
  have h1 : (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y =
            (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y' := by
    have := congrArg (fun v => v ∘ e.symm) h
    simpa [chg_apply, Function.comp_def] using this
  have h2 := congrArg
    (fun v => ((P⁻¹ : GL (Fin a ⊕ Fin b) ℂ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ v) h1
  simpa [mulVec_mulVec] using h2

lemma qf_chg {a b : ℕ} (J : Matrix n n ℂ) (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ)
    (h : cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Jpq a b) (y : Fin a ⊕ Fin b → ℂ) :
    qf J (chg e P y) = star y ⬝ᵥ Jpq a b *ᵥ y := by
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ :=
    (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ)
  have hc : cT (starRingEnd ℂ) M = Mᴴ := by ext i j; rfl
  rw [← h, hc]
  set w := M *ᵥ y
  have h1 : J *ᵥ (w ∘ e) = (J.reindex e e *ᵥ w) ∘ e := by
    rw [reindex_apply, submatrix_mulVec_equiv]
    ext i; simp [Function.comp_def]
  have h2 : qf J (chg e P y) = star w ⬝ᵥ (J.reindex e e *ᵥ w) := by
    rw [qf, chg_apply, h1]
    simp only [dotProduct, Function.comp_apply, Pi.star_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [h2]
  simp only [w, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, Matrix.mul_assoc]

lemma jpq_inl (a b : ℕ) (z : Fin a → ℂ) :
    star (inlMap a b z) ⬝ᵥ Jpq a b *ᵥ inlMap a b z = star z ⬝ᵥ z := by
  simp [inlMap, Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def]

lemma jpq_inr (a b : ℕ) (z : Fin b → ℂ) :
    star (inrMap a b z) ⬝ᵥ Jpq a b *ᵥ inrMap a b z = -(star z ⬝ᵥ z) := by
  simp [inrMap, Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def,
    neg_mulVec, Finset.sum_neg_distrib]

lemma pos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b} {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inlMap a b)) (hx0 : x ≠ 0) : 0 < qf J x := by
  obtain ⟨z, rfl⟩ := hx
  have hz : z ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
  rw [LinearMap.comp_apply, qf_chg J e P h, jpq_inl]
  exact dotProduct_star_self_pos_iff.mpr hz

lemma nonpos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b}
    {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inrMap a b)) : qf J x ≤ 0 := by
  obtain ⟨z, rfl⟩ := hx
  rw [LinearMap.comp_apply, qf_chg J e P h, jpq_inr]
  exact neg_nonpos.mpr (dotProduct_star_self_nonneg z)

/-- 惯性指数的正部单调性：若 `J` 同时有签名 `(a,b)` 与 `(a',b')`，则 `a ≤ a'`。 -/
theorem fst_le_of_hasSignature {J : Matrix n n ℂ} {a b a' b' : ℕ}
    (h : HasSignature J a b) (h' : HasSignature J a' b') : a ≤ a' := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  by_contra hlt
  push Not at hlt
  set U := LinearMap.range (chg e P ∘ₗ inlMap a b)
  set N := LinearMap.range (chg e' P' ∘ₗ inrMap a' b')
  have hU : finrank ℂ U = a := by
    rw [LinearMap.finrank_range_of_inj
      (by rw [LinearMap.coe_comp]; exact (chg_injective e P).comp (inlMap_injective a b))]
    simp
  have hN : finrank ℂ N = b' := by
    rw [LinearMap.finrank_range_of_inj
      (by rw [LinearMap.coe_comp]; exact (chg_injective e' P').comp (inrMap_injective a' b'))]
    simp
  have hcard : Fintype.card n = a' + b' := by simpa using Fintype.card_congr e'
  have hsup : finrank ℂ ↥(U ⊔ N) ≤ Fintype.card n := by
    have := Submodule.finrank_le (U ⊔ N)
    simpa using this
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U N
  have hinf : U ⊓ N ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hsum
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  have h1 := pos_of_mem hP (Submodule.mem_inf.1 hx).1 hx0
  have h2 := nonpos_of_mem hP' (Submodule.mem_inf.1 hx).2
  exact lt_irrefl _ (lt_of_lt_of_le h1 h2)

/-- Sylvester 惯性律：正部的个数唯一（归档侧 `hasSignature_fst_unique`，此处对一般 `n` 陈述）。 -/
theorem hasSignature_fst_unique {J : Matrix n n ℂ} {a b a' b' : ℕ}
    (h : HasSignature J a b) (h' : HasSignature J a' b') : a = a' :=
  le_antisymm (fst_le_of_hasSignature h h') (fst_le_of_hasSignature h' h)

/-- 签名下的总维数固定：`card n = a + b`。 -/
theorem card_eq_of_hasSignature {J : Matrix n n ℂ} {a b : ℕ}
    (h : HasSignature J a b) : Fintype.card n = a + b := by
  obtain ⟨e, -, -⟩ := h
  have := Fintype.card_congr e
  simpa using this

/-- **签名（惯性指数）的唯一性**：`J` 的签名作为有序对是良定义的。
    这条是我们在本侧真正要用的形式：`(p, q)` 不是依赖选取的量，
    而是矩阵的不变量，因此「谱对偶的符号差」可以被当作确定的对象搬运。
    归档侧只证了正部（`fst_le_of_hasSignature` 两次）；负部由总维数补出。 -/
theorem hasSignature_unique {J : Matrix n n ℂ} {a b a' b' : ℕ}
    (h : HasSignature J a b) (h' : HasSignature J a' b') : a = a' ∧ b = b' := by
  have ha : a = a' := hasSignature_fst_unique h h'
  have hc : Fintype.card n = a + b := card_eq_of_hasSignature h
  have hc' : Fintype.card n = a' + b' := card_eq_of_hasSignature h'
  have hb : b = b' := by omega
  exact ⟨ha, hb⟩

/-! ### 第二、三条可复用引理（同样照抄归档侧，纯矩阵层、无 sorry）

`hasSignature_of_frame`：只要有合同变换把 `J` 化成 `Jpq p q`，签名即成立——
把"签名"从存在性定义降成**可计算判据**。
`sylvester_le`：任何使二次型 `≤ 0` 的（单射）子空间，维数不超过 `q`。
这是 Sylvester 惯性律的**反向用法**：它不是去证明签名唯一，而是给出
「负向维数上界」，正是我们给 A 矩阵做符号差估计时缺的那条。 -/

/-- 共轭转置与 `cT` 一致（`σ = starRingEnd ℂ`）。 -/
theorem cT_conj_eq {m p : Type} (M : Matrix m p ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT]

/-- `Jpq` 二次型的显式展开：正部减负部。 -/
theorem form_Jpq (p q : ℕ) (y : Fin p ⊕ Fin q → ℂ) :
    star y ⬝ᵥ (Jpq p q *ᵥ y) =
      (∑ i, star (y (Sum.inl i)) * y (Sum.inl i)) - ∑ j, star (y (Sum.inr j)) * y (Sum.inr j) := by
  unfold Jpq
  simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec,
    Function.comp_def, sub_eq_add_neg]

private theorem conjTranspose_submatrix_mul_mul_submatrix {R k l m : Type} [CommRing R] [StarRing R]
    [Fintype k] (B : Matrix k l R) (M : Matrix k k R) (f : m → l) :
    (B.submatrix id f)ᴴ * M * B.submatrix id f = (Bᴴ * M * B).submatrix f f := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem Jpq_det_ne_zero (p q : ℕ) : (Jpq p q).det ≠ 0 := by
  unfold Jpq
  rw [Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_neg]

private theorem conjTranspose_submatrix_mul_reindex_mul_submatrix {n k : Type} [Fintype n] [Fintype k]
    (e : n ≃ k) (Q : Matrix n k ℂ) (J : Matrix n n ℂ) :
    (Q.submatrix e.symm id)ᴴ * J.reindex e e * Q.submatrix e.symm id = Qᴴ * J * Q := by
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

/-- **帧判据**：若存在 `Q` 使 `Qᴴ J Q = Jpq p q` 且 `card n = p + q`，则 `J` 有签名 `(p,q)`。 -/
theorem hasSignature_of_frame {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (hn : Fintype.card n = p + q) (Q : Matrix n (Fin p ⊕ Fin q) ℂ) (hQ : Qᴴ * J * Q = Jpq p q) :
    HasSignature J p q := by
  classical
  have hc : Fintype.card n = Fintype.card (Fin p ⊕ Fin q) := by simp [hn]
  obtain ⟨e⟩ : Nonempty (n ≃ Fin p ⊕ Fin q) := ⟨Fintype.equivOfCardEq hc⟩
  have hP := conjTranspose_submatrix_mul_reindex_mul_submatrix e Q J
  rw [hQ] at hP
  have hdet : (Q.submatrix e.symm id).det ≠ 0 := by
    intro h0
    apply Jpq_det_ne_zero p q
    rw [← hP, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hu : IsUnit (Q.submatrix e.symm id) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨e, hu.unit, ?_⟩
  rw [IsUnit.unit_spec, cT_conj_eq]
  exact hP

/-- **负向维数上界**（归档侧 `sylvester_le`）：签名 `(p,q)` 的 `J` 上，
任何二次型 `≤ 0` 的单射子空间维数不超过 `q`。
注意 `hneg` 用 `(… ).re ≤ 0`：复数上没有全域序，只取实部——这是我们
搬运时必须保留的口径，否则会与 `Complex` 上的条件序混淆。 -/
theorem sylvester_le {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (J : Matrix n n ℂ) {p q : ℕ} (hJ : HasSignature J p q) (B : Matrix n k ℂ)
    (hB : Function.Injective B.mulVec)
    (hneg : ∀ v : k → ℂ, (star (B *ᵥ v) ⬝ᵥ (J *ᵥ (B *ᵥ v))).re ≤ 0) : Fintype.card k ≤ q := by
  classical
  obtain ⟨e, P, hP⟩ := hJ
  rw [cT_conj_eq] at hP
  by_contra hcon
  push Not at hcon
  let T : (k → ℂ) →ₗ[ℂ] (Fin q → ℂ) := (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) ∘ₗ
    (LinearMap.funLeft ℂ ℂ e.symm) ∘ₗ (Matrix.mulVecLin B)
  have hker : LinearMap.ker T ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]
    exact hcon
  obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hTv : T v = 0 := LinearMap.mem_ker.1 hvK
  have hyr : ∀ j, (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      ((B *ᵥ v) ∘ e.symm)) (Sum.inr j) = 0 := fun j => congrFun hTv j
  set w : n → ℂ := B *ᵥ v with hwdef
  set y : Fin p ⊕ Fin q → ℂ :=
    ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (w ∘ e.symm) with hydef
  have hw : w ∘ e.symm = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ y := by
    rw [hydef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hwne : w ≠ 0 := by
    intro h
    apply hv0
    apply hB
    show B *ᵥ v = B *ᵥ 0
    rw [Matrix.mulVec_zero]
    exact h
  have hyne : y ≠ 0 := by
    intro h
    apply hwne
    funext i
    have h3 := congrFun hw (e i)
    rw [h, Matrix.mulVec_zero] at h3
    simpa using h3
  obtain ⟨i, hi⟩ : ∃ i, y (Sum.inl i) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hyne
    funext s
    cases s with
    | inl i => exact hall i
    | inr j => exact hyr j
  have h1 : star w ⬝ᵥ (J *ᵥ w) = star (w ∘ e.symm) ⬝ᵥ (J.reindex e e *ᵥ (w ∘ e.symm)) := by
    simp only [dotProduct, mulVec, Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply,
      Pi.star_apply]
    refine Fintype.sum_equiv e _ _ (fun a => ?_)
    simp only [Equiv.symm_apply_apply]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun b => by simp only [Equiv.symm_apply_apply])
  have hform : star w ⬝ᵥ (J *ᵥ w) = star y ⬝ᵥ (Jpq p q *ᵥ y) := by
    rw [h1, hw, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hP]
  have hre : ∀ z : ℂ, (star z * z).re = Complex.normSq z := fun z => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have hpos : 0 < (star w ⬝ᵥ (J *ᵥ w)).re := by
    rw [hform, form_Jpq]
    simp only [hyr, mul_zero, Finset.sum_const_zero, sub_zero, Complex.re_sum, hre]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have := hneg v
  linarith

/-! ### 第四条：`hasSignature_fromBlocks`（A 分块拼装）

`A = diag(A₁, A₂) ⟹ sig(A) = (p₁+p₂, q₁+q₂)`。这是谱对偶里唯一还缺的拼装件：
把大矩阵的符号差规约成两块小矩阵的符号差，之后所有"符号差估计"都可以
分块做、再相加，而不必整体处理。

连带搬两条支撑件：
* `card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature`：从签名**反造**出合同变换 `Q`
  （`Qᴴ J Q = Jpq p q` 且 `card n = p + q`）。这条比 `hasSignature_of_frame` 更实用，
  因为它给你一个**可用的 `Q`**，而不只是存在性。
* `Jpq_eq_diagonal_elim_one_neg_one`：`Jpq p q = diagonal (Sum.elim 1 (-1))`，
  分块拼装时把三个 `Jpq` 统一成对角的依据。 -/

/-- 从签名反造合同变换：`card n = p + q` 且存在显式 `Q` 使 `Qᴴ * J * Q = Jpq p q`。 -/
theorem card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature {J : Matrix n n ℂ} {p q : ℕ}
    (h : HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by simpa using Fintype.card_congr e, (P : Matrix _ _ ℂ).submatrix e id, ?_⟩
  rw [cT_conj_eq] at hP
  rw [← hP, ← conjTranspose_submatrix_mul_reindex_mul_submatrix e ((P : Matrix _ _ ℂ).submatrix e id) J]
  simp

/-- 签名矩阵的对角形式：`Jpq p q = diagonal (Sum.elim (fun _ ↦ 1) (fun _ ↦ -1))`。 -/
theorem Jpq_eq_diagonal_elim_one_neg_one (p q : ℕ) :
    Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext (i | i) (j | j)
  · by_cases h : i = j <;> simp [Jpq, h]
  · simp [Jpq]
  · simp [Jpq]
  · by_cases h : i = j <;> simp [Jpq, h]

/-- **分块拼装**：`sig(G) = (p,q)`、`sig(H) = (p',q')` ⟹ `sig(diag(G,H)) = (p+p', q+q')`。 -/
theorem hasSignature_fromBlocks {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G : Matrix n n ℂ} {H : Matrix m m ℂ} {p q p' q' : ℕ}
    (hG : HasSignature G p q) (hH : HasSignature H p' q') :
    HasSignature (fromBlocks G 0 0 H) (p + p') (q + q') := by
  classical
  obtain ⟨hn, Q1, hQ1⟩ := card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature hG
  obtain ⟨hm, Q2, hQ2⟩ := card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature hH
  obtain ⟨σ, hσ⟩ : ∃ σ : (Fin p ⊕ Fin q) ⊕ (Fin p' ⊕ Fin q') ≃ Fin (p + p') ⊕ Fin (q + q'),
      σ = (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) :=
    ⟨_, rfl⟩
  apply hasSignature_of_frame (by rw [Fintype.card_sum, hn, hm]; omega)
    ((Matrix.fromBlocks Q1 0 0 Q2).submatrix id σ.symm)
  rw [conjTranspose_submatrix_mul_mul_submatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hQ1, hQ2]
  rw [Jpq_eq_diagonal_elim_one_neg_one, Jpq_eq_diagonal_elim_one_neg_one,
    Jpq_eq_diagonal_elim_one_neg_one, Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨y, rfl⟩ := σ.surjective x
  rcases y with (a | a) | (a | a) <;> simp [hσ]

end OrderPreservingBijection.SylvesterInertia

/-! ### 审计段：本模块定理的 axiom 集（搬运忠实度实测）

期望四条全部为 `[propext, Classical.choice, Quot.sound]`，即**无 sorryAx**。
若出现 `sorryAx` 或 `Lean.ofReduceBool`，说明搬运过程中被弱化，必须回退重查。 -/

open OrderPreservingBijection.SylvesterInertia in
#print axioms fst_le_of_hasSignature
open OrderPreservingBijection.SylvesterInertia in
#print axioms hasSignature_fst_unique
open OrderPreservingBijection.SylvesterInertia in
#print axioms card_eq_of_hasSignature
open OrderPreservingBijection.SylvesterInertia in
#print axioms hasSignature_unique
open OrderPreservingBijection.SylvesterInertia in
#print axioms hasSignature_of_frame
open OrderPreservingBijection.SylvesterInertia in
#print axioms sylvester_le
open OrderPreservingBijection.SylvesterInertia in
#print axioms card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature
open OrderPreservingBijection.SylvesterInertia in
#print axioms Jpq_eq_diagonal_elim_one_neg_one
open OrderPreservingBijection.SylvesterInertia in
#print axioms hasSignature_fromBlocks






