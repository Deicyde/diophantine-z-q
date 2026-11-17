/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom (git blob 0b8e16d1ee8613cabf97db8f84237ed2a2adf146, sha256 40e587b0e16ae3a31ad083d79b87e1d7cbbe889cedfbe1b92626048712242212).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve

theorem ModularCurve.genusFF_qExpFunctionFieldC_eq_of_ringHom
    {K₀ K : Type*} [Field K₀] [Field K] [IsAlgClosed K₀] [IsAlgClosed K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hfg : ∃ x : ModularCurve.qExpFunctionFieldC K₀ Γ, Transcendental K₀ x ∧
      FiniteDimensional
        (IntermediateField.adjoin K₀ ({x} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
        (ModularCurve.qExpFunctionFieldC K₀ Γ)) :
    AlgebraicCurve.genusFF K (ModularCurve.qExpFunctionFieldC K Γ) =
      AlgebraicCurve.genusFF K₀ (ModularCurve.qExpFunctionFieldC K₀ Γ) := by
  revert K₀ K φ Γ hfg
  exact @_root_.P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.solution
