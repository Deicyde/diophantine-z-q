/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer (git blob 31900f55d737d17c3d6fcd40b047f52b794669be, sha256 1c4be561a0fa91a933f76b81f0ecb23b0c9c99b705158039c2977c1b8f82c3f9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
    (hsep : ∀ τ τ' : UpperHalfPlane, D.pt τ = D.pt τ' → ∃ γ ∈ Γ, γ • τ = τ')
    (τ : UpperHalfPlane) :
    2 * D.ramification τ =
      Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) := by
  revert Γ hT F₀ hF D hsep τ
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.solution
