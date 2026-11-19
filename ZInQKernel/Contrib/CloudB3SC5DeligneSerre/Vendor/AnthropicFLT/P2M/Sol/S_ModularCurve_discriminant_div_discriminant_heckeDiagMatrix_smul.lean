/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul (git blob d09025b8c110ec4362fc5a02c3882aabd73ac0c9, sha256 4fae7263e56672e62b9c05970e76a9b51839cae74d3dab7d0da342fd448d9442).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace ModularCurve
export _root_.ModularCurve (exists_sl2_heckeDiagMatrix_smul_eq)
open _root_.ModularCurve

namespace QexpN

theorem discriminant_div_discriminant_heckeDiagMatrix_smul' (N : ℕ) [NeZero N]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (τ : UpperHalfPlane) :
    ModularForm.discriminant (γ • τ)
        / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • γ • τ)
      = ModularForm.discriminant τ
        / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := by
  obtain ⟨γ', hact, hden⟩ := ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq N γ hγ
  have hγSL : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hγ'SL : (mapGL ℝ γ' : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ', rfl⟩
  have hΔγ : ModularForm.discriminant (γ • τ)
      = UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) ^ (12 : ℤ)
        * ModularForm.discriminant τ := by
    have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγSL τ
    simp [CuspForm.coe_discriminant] at h
    exact h
  have hΔγ' : ModularForm.discriminant (γ' • ModularForm.heckeDiagMatrix N • τ)
      = UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ)
          (((ModularForm.heckeDiagMatrix N • τ : UpperHalfPlane)) : ℂ) ^ (12 : ℤ)
        * ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := by
    have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ'SL
        (ModularForm.heckeDiagMatrix N • τ)
    simp [CuspForm.coe_discriminant] at h
    exact h
  rw [hact τ, hΔγ, hΔγ', hden τ,
    mul_div_mul_left _ _ (zpow_ne_zero 12 (UpperHalfPlane.denom_ne_zero _ _))]

end QexpN

end ModularCurve

end

theorem solution (N : ℕ) [NeZero N] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) : ModularForm.discriminant (γ • τ) / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • γ • τ) = ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) :=
  ModularCurve.QexpN.discriminant_div_discriminant_heckeDiagMatrix_smul' N γ hγ τ
