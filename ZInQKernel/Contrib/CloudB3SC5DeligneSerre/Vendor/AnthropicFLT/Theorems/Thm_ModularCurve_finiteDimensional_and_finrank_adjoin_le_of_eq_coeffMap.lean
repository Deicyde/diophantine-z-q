/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap (git blob 560946de46b7b4b0b2aefd793f07483ac683545f, sha256 5b784415ddda6b47d7969a5233c751f9ae4bebececcf8bb23e1fc3eda387bb67).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups in

theorem ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))
    (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx₀ : Transcendental K₀ (x₀ : LaurentSeries K₀))
    (hx : (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀))
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
      (ModularCurve.qExpFunctionFieldC K Γ)] :
    FiniteDimensional (IntermediateField.adjoin K₀ ({x₀} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
        (ModularCurve.qExpFunctionFieldC K₀ Γ) ∧
      Module.finrank (IntermediateField.adjoin K₀ ({x₀} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
          (ModularCurve.qExpFunctionFieldC K₀ Γ) ≤
        Module.finrank (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) := by
  revert K₀ K φ Γ x₀ x hx₀ hx
  exact @_root_.P2MW.S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap.solution
