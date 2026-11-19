/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three (git blob c70c08fd853fb2cde3c5a2aa015fffa7de6549e4, sha256 5973acd52b4d349891285578d95a978bb33830b47fb8ef8bd5e3c4d0dab7bdb1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_addMonoidHom_i_tau_vcInvFun_of_char_three
    {K : Type*} [Field K] [DecidableEq K] [CharP K 3] (i : Kˣ) (hi : (i : K) ^ 2 = -1) :
    ∃ α β : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
        (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
      (∀ T, HEq (Point.vcInvFun (⟨i, 0, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (α T)) ∧
      (∀ T, HEq (Point.vcInvFun (⟨1, 1, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (β T)) ∧
      (∀ T, α (α T) = -T) ∧ (∀ T, β (β T) + β T + T = 0) ∧ (∀ T, α (β T) = β (β (α T))) ∧
      (∀ γ : VariableChange K,
          γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 0, -1, 0⟩ →
        ∃ m : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨
              m = α.comp (β.comp β)) ∧
          ((∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) ∨
            (∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T)
              (-(m T))))) ∧
      (∀ m : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨
              m = α.comp (β.comp β)) →
        ∃ γ : VariableChange K, γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 0, -1, 0⟩ ∧
          ∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) := by
  revert K i hi
  exact @_root_.P2MW.S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.solution
