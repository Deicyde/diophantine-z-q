/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one (git blob 7b26131a4bc99a0fcb3f15eb55a626dc722533cc, sha256 0721804c553d4fdd514a6755192d82e899caf6620c7f60c03ce364071a23e74d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.FrickeGamma1
end P2MW.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.FrickeGamma1

namespace P2MW.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one

set_option autoImplicit false

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace FrickeGamma1

open ConjAct Pointwise



variable (M : ℕ) [NeZero M]

noncomputable def frickeGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL : ((frickeGL M).det : ℝ) = M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

theorem det_frickeGL_pos : 0 < ((frickeGL M).det : ℝ) := by
  rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)

variable {M}

def frickeConj (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -(γ 1 0 / M); -(M * γ 0 1), γ 0 0], by
    rw [Matrix.det_fin_two_of]
    have h1 := Matrix.det_fin_two γ.1
    rw [γ.2] at h1
    obtain ⟨c', hc'⟩ := hγ
    have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    rw [hc', Int.mul_ediv_cancel_left _ hM]
    rw [hc'] at h1
    linear_combination (-1 : ℤ) * h1⟩

theorem frickeConj_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    ∃ hd : (M : ℤ) ∣ γ 1 0, frickeConj γ hd ∈ Gamma1 M := by
  rw [Gamma1_mem] at hγ
  obtain ⟨ha, hd, hc⟩ := hγ
  have hdvd : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 hc
  refine ⟨hdvd, ?_⟩
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · show (((γ 1 1 : ℤ)) : ZMod M) = 1; exact hd
  · show (((γ 0 0 : ℤ)) : ZMod M) = 1; exact ha
  · show (((-(M * γ 0 1) : ℤ)) : ZMod M) = 0
    rw [Int.cast_neg, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, neg_zero]

theorem coe_frickeConj (γ : SL(2, ℤ)) (c' : ℤ) (hc' : γ 1 0 = M * c') :
    ((frickeConj γ ⟨c', hc'⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 1 1, -c'; -(M * γ 0 1), γ 0 0] := by
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hq : γ 1 0 / M = c' := by rw [hc', Int.mul_ediv_cancel_left _ hM]
  simp [frickeConj, hq]

theorem frickeGL_mul_coe (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * (γ : GL (Fin 2) ℝ) = ((frickeConj γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) * frickeGL M := by
  obtain ⟨c', hc'⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_frickeConj γ c' hc', hc'] <;> ring

theorem coe_mul_frickeGL (γ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) :
    (γ : GL (Fin 2) ℝ) * frickeGL M = frickeGL M * ((frickeConj γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  obtain ⟨c', hc'⟩ := hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_frickeConj γ c' hc', hc'] <;> ring

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem mem_map_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (γ : GL (Fin 2) ℝ) = x :=
  Subgroup.mem_map

theorem frickeGL_mul_mul_inv_mem {x : GL (Fin 2) ℝ} (hx : x ∈ (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :
    frickeGL M * x * (frickeGL M)⁻¹ ∈ (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_map_Gamma1_iff x).1 hx
  obtain ⟨hd, hmem⟩ := frickeConj_mem_Gamma1 hγ
  rw [frickeGL_mul_coe γ hd, mul_inv_cancel_right]
  exact (mem_map_Gamma1_iff _).2 ⟨_, hmem, rfl⟩

theorem frickeGL_inv_mul_mul_mem {x : GL (Fin 2) ℝ} (hx : x ∈ (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :
    (frickeGL M)⁻¹ * x * frickeGL M ∈ (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_map_Gamma1_iff x).1 hx
  obtain ⟨hd, hmem⟩ := frickeConj_mem_Gamma1 hγ
  rw [mul_assoc, coe_mul_frickeGL γ hd, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (mem_map_Gamma1_iff _).2 ⟨_, hmem, rfl⟩

theorem toConjAct_frickeGL_inv_smul :
    toConjAct (frickeGL M)⁻¹ • (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) = (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro h
    have := frickeGL_inv_mul_mul_mem h
    rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] at this
  · exact frickeGL_mul_mul_inv_mem

theorem coe_frickeGL_smul (τ : ℍ) : (↑(frickeGL M • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

theorem denom_frickeGL (τ : ℍ) : UpperHalfPlane.denom (frickeGL M) τ = (M : ℂ) * (τ : ℂ) := by
  simp [UpperHalfPlane.denom]

theorem slash_frickeGL_apply (f : ℍ → ℂ) (k : ℤ) (τ : ℍ) :
    (f ∣[k] frickeGL M) τ = (M : ℂ)⁻¹ * (τ : ℂ) ^ (-k) * f (frickeGL M • τ) := by
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos (det_frickeGL_pos M), det_frickeGL,
    denom_frickeGL]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [ContinuousAlgEquiv.refl_apply,
    abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M) : (0 : ℝ) < M),
    Complex.ofReal_natCast, mul_zpow, zpow_neg (M : ℂ) k, zpow_sub_one₀ hM]
  field_simp

noncomputable def frickeForm {k : ℤ} (g : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k :=
  ((M : ℝ) • CuspForm.translate g (frickeGL M)).copy
    (fun τ => (τ : ℂ) ^ (-k) * g (frickeGL M • τ))
    (by
      funext τ
      rw [CuspForm.coe_smul, Pi.smul_apply, CuspForm.translate]
      show _ = (M : ℝ) • ((⇑g ∣[k] frickeGL M) τ)
      rw [slash_frickeGL_apply, Complex.real_smul, Complex.ofReal_natCast]
      have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
      field_simp)
    (toConjAct_frickeGL_inv_smul).symm

theorem frickeForm_apply {k : ℤ} (g : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) (τ : ℍ) :
    frickeForm g τ = (τ : ℂ) ^ (-k) * g (frickeGL M • τ) := rfl

theorem eq_frickeGL_smul {τ τ' : ℍ} (h : (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1) :
    τ' = frickeGL M • τ := by
  apply UpperHalfPlane.ext
  rw [coe_frickeGL_smul]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp
  linear_combination h

theorem apply_eq_zpow_mul_frickeForm {k : ℤ} (g : CuspForm (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) {τ τ' : ℍ}
    (h : (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1) :
    g τ' = (τ : ℂ) ^ k * frickeForm g τ := by
  rw [frickeForm_apply, eq_frickeGL_smul h, ← mul_assoc, ← zpow_add₀ (UpperHalfPlane.ne_zero τ),
    add_neg_cancel, zpow_zero, one_mul]

end FrickeGamma1
open scoped _root_.P2MW.S_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one.FrickeGamma1

theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (g : CuspForm (Gamma1 M) k) :
    ∃ h : CuspForm (Gamma1 M) k,
      ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = (τ : ℂ) ^ k * h τ :=
  ⟨FrickeGamma1.frickeForm g, fun _ _ h => FrickeGamma1.apply_eq_zpow_mul_frickeForm g h⟩
