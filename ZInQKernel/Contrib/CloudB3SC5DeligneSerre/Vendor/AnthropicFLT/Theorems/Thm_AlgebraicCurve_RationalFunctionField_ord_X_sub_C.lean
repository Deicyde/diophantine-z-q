/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C (git blob 3aa1d97091bdd14db4b6567231d85e6e079ccb02, sha256 fd9a57b63006161b55f817ba15a6bb907c829b1aebb1a079513f70bcd5350eea).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_X_sub_C

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.ord_X_sub_C (K : Type*) [Field K] [DecidableEq (RatFunc K)] (b : K) (v : Place K (RatFunc K)) : v.ord (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C b)) = (Finsupp.single (placeOfPoint K b) (1 : ℤ) + Finsupp.single (placeInfty K) (-1 : ℤ)) v := by
  revert K b v
  exact @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_X_sub_C.solution
