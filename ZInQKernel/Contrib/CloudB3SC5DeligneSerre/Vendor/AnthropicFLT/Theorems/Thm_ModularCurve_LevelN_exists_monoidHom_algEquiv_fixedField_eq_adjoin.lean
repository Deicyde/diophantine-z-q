/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin (git blob 4f20271c79552a988a099a4920fa9eee3530c417, sha256 b42cc97a3da5903fb1fc455840e9f65b89bc05a3dba28ca5616c164eed2185b6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ (hst : ∀ γ : SL(2, ℤ), ∀ F ∈ ModularCurve.LevelN.ring N,
        (fun τ : UpperHalfPlane => F (γ • τ)) ∈ ModularCurve.LevelN.ring N)
      (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K)),
      (∀ (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
          σ γ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
            algebraMap (ModularCurve.LevelN.ring N) K
              ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst γ⁻¹ F hF⟩) ∧
      σ.ker = CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ∧
      IntermediateField.fixedField σ.range =
        IntermediateField.adjoin ℂ
          ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K) ∧
      Transcendental ℂ (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ∧
      FiniteDimensional
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K ∧
      Module.finrank
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K =
        (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      IsGalois
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K := by
  revert N K
  exact @_root_.P2MW.S_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.solution
