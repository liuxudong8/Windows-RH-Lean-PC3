import A5CharQ5.A5Defs

open Representation

noncomputable section

def rhoHom : G →* ((Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) where
  toFun := ρG
  map_one' := ρG.map_one'
  map_mul' := ρG.map_mul'

lemma icosahedralS_ne_one_mat : icosahedralS ≠ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [icosahedralS] at h01

lemma ρG_sG_ne_one (h : ρG sG = 1) : False := by
  have hρ : ρG sG = Matrix.toLin' icosahedralS := by simp [ρG, psi_sG, ρP_pA_eq]
  rw [hρ] at h
  have hv := LinearMap.congr_fun h (Pi.single (1 : Fin 3) (1 : ℂ))
  have h0 := congrFun hv 0
  simp [Matrix.toLin'_apply, icosahedralS, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Pi.single] at h0

lemma ρG_ker_eq_bot : MonoidHom.ker rhoHom = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.normal_ker rhoHom) with h | h
  · exact h
  · exfalso
    have hs : sG ∈ MonoidHom.ker rhoHom := by rw [h]; exact Subgroup.mem_top sG
    exact ρG_sG_ne_one ((MonoidHom.mem_ker).mp hs)
