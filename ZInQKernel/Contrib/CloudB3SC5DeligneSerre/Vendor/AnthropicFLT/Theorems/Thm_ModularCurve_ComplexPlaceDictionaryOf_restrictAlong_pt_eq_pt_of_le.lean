/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_eq_pt_of_le (git blob 955a7435c5901dd105dda47eb0b2353674912215, sha256 e0c55dda99202adaf4b8eeca833d7573ba5935d53c631d19ece6ac3cff400f98).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_eq_pt_of_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.restrictAlong_pt_eq_pt_of_le
    {Γ Γ' : Subgroup SL(2, ℤ)} (hle : Γ' ≤ Γ) (hT : ModularGroup.T ∈ Γ')
    {F₀ F₀' : IntermediateField ℚ (LaurentSeries ℚ)} (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (D' : ModularCurve.ComplexPlaceDictionaryOf Γ' F₀')
    (ι : ↥(ModularCurve.laurentBaseChange ℂ F₀) →ₐ[ℂ] ↥(ModularCurve.laurentBaseChange ℂ F₀'))
    (hι : ∀ x : ModularCurve.laurentBaseChange ℂ F₀,
      ((ι x : ModularCurve.laurentBaseChange ℂ F₀') : LaurentSeries ℂ) = (x : LaurentSeries ℂ))
    (hint : ι.toRingHom.IsIntegral) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong ι hint = D.pt τ := by
  revert Γ Γ' hle hT F₀ F₀' hF D D' ι hι hint τ
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_eq_pt_of_le.solution
