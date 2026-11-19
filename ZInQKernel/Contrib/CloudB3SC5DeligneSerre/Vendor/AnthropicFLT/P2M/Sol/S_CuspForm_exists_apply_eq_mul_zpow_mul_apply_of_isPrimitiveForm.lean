/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm (git blob 90035c2928711effb2290aa3e0990fe77a53fd38, sha256 9ebaf501b6e269724a863a571c55f3e5953fa71864a70b1988c17dac8ccf6e88).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.FrickePseudoEigenvalue
end P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.FrickePseudoEigenvalue

namespace P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

noncomputable section

namespace FrickePseudoEigenvalue

def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL (M : ℕ) [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos (M : ℕ) [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  linarith

theorem frickeGL_smul_mul (M : ℕ) [NeZero M] (τ : ℍ) :
    ((frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]
  field_simp

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

omit [NeZero M] in
theorem ne_zero_of_isPrimitiveForm {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (hg : CuspForm.IsPrimitiveForm ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.isEigenformWith.qCoeff_one
  rw [h0, CuspForm.coe_zero, qCoeff_zero_fun] at h1
  exact zero_ne_one h1

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, qCoeff g' n = conj (qCoeff g n)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ τ τ' : ℍ, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 → g τ' = c * (τ : ℂ) ^ k * g' τ := by
  have hg0 : g ≠ 0 := ne_zero_of_isPrimitiveForm hg
  have heig := hg.isEigenformWith

  obtain ⟨h, hh⟩ := CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one M k g

  obtain ⟨hneb, hhecke⟩ :=
    CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke M k ε g h heig.hasNebentypus hh

  have hadj : ∀ p : ℕ, p.Prime → ¬ p ∣ M →
      conj (qCoeff g p) = ε⁻¹ (p : ZMod M) * qCoeff g p := fun p hp hpM =>
    CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M k ε g hg0 heig.hasNebentypus p hp hpM
      (qCoeff g p) (heig.hecke_of_not_dvd hp hpM)

  have hg'prim : CuspForm.IsPrimitiveForm ε⁻¹ g' :=
    CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj M k ε g hg g' hg'

  have hmult : h = qCoeff h 1 • g' := by
    refine CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen M k ε⁻¹ g' hg'prim h hneb ∅
      (fun p hp _ hpM n => ?_)
    rw [hg' p, hadj p hp hpM]
    exact hhecke p hp hpM (qCoeff g p) (heig.hecke_of_not_dvd hp hpM) n

  refine ⟨qCoeff h 1, fun hc => hg0 ?_, fun τ τ' hτ => ?_⟩
  ·
    rw [hc, zero_smul] at hmult
    apply DFunLike.ext
    intro τ'
    have key := hh (frickeGL M • τ') τ' (by
      have := frickeGL_smul_mul M τ'
      linear_combination this)
    rw [key, hmult, CuspForm.zero_apply, mul_zero, CuspForm.zero_apply]
  · have hpt : h τ = qCoeff h 1 * g' τ := by
      have := congrArg (fun F : CuspForm (Gamma1 M) k => F τ) hmult
      simpa only [CuspForm.IsGLPos.smul_apply, smul_eq_mul] using this
    rw [hh τ τ' hτ, hpt]
    ring

end FrickePseudoEigenvalue
open scoped _root_.P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.FrickePseudoEigenvalue

end
open scoped _root_.P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.FrickePseudoEigenvalue

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = c * (τ : ℂ) ^ k * g' τ :=
  FrickePseudoEigenvalue.main ε g hg g' hg'
