/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint (git blob 89bfbeec15d235a3b9f79b1f4a2475b685436dfa, sha256 f21f16938801b7a7756e74e289ffafdb7d370597fb9f14a742f4f54fb9dd1231).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem AlgebraicCurve.Place.ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint
    {K F : Type*} [Field K] [Field F] [Algebra K F] [DecidableEq (RatFunc K)]
    (φ : RatFunc K →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F) (a : K)
    (hwa : w.restrictAlong φ hφ = AlgebraicCurve.RationalFunctionField.placeOfPoint K a) :
    (AlgebraicCurve.Place.ramificationIndexAlong φ w : ℤ) =
      w.ord (φ (RatFunc.X : RatFunc K) - algebraMap K F a) := by
  revert K F φ hφ w a hwa
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint.solution
