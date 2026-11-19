/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap (git blob 67acde22f814d784a8a7f8d908c0e291270e0f02, sha256 a7dc7d1cf4d3f1c389391fad3bacd7cb26bb21226440b83e766ddb545d10d07a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (σ₀ : ModularCurve.qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] ModularCurve.qExpFunctionFieldC K₀ Γ) :
    ∃! σ : ModularCurve.qExpFunctionFieldC K Γ ≃ₐ[K] ModularCurve.qExpFunctionFieldC K Γ,
      ∀ (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ),
        (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀) →
        ((σ x : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K) =
          ModularCurve.coeffMap φ ((σ₀ x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) : LaurentSeries K₀) := by
  revert K₀ K φ Γ σ₀
  exact @_root_.P2MW.S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap.solution
