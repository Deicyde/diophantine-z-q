/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand (git blob 47cb8a2d7f0177b4418ba9d219bdc278b168c561, sha256 610921da52997e753ffcc24b6f4a96a42ba54be6793b5ba2703e1f9ec2780db8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.restrictAlong_pt_qExpand
    (Γ Γ' : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (hT' : ModularGroup.T ∈ Γ')
    (ℓ : ℕ) [NeZero ℓ] (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (ModularForm.heckeDiagMatrix ℓ))
    (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (D' : ModularCurve.ComplexPlaceDictionaryOf Γ' F₁)
    (β : ModularCurve.laurentBaseChange ℂ F₀ →ₐ[ℂ] ModularCurve.laurentBaseChange ℂ F₁)
    (hβq : ∀ x : ModularCurve.laurentBaseChange ℂ F₀,
      ((β x : ModularCurve.laurentBaseChange ℂ F₁) : LaurentSeries ℂ) =
        ModularCurve.qExpand ℂ ℓ (x : LaurentSeries ℂ))
    (hβ : β.toRingHom.IsIntegral) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong β hβ = D.pt (ModularForm.heckeDiagMatrix ℓ • τ) ∧
      D'.ramification τ * (D'.pt τ).ramificationIndexAlong β =
        D.ramification (ModularForm.heckeDiagMatrix ℓ • τ) := by
  revert Γ Γ' hT hT' ℓ hΓ' F₀ F₁ D D' β hβq hβ τ
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.solution
