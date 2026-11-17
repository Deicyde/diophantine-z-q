/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one (git blob 4bd87be9b2eca405c6f6f97a4ad2b7477fe66a7f, sha256 eaa122ea66468949cb3e2a6b0d17a4c9a808eba3a3de162705eb852112a86768).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {f : F} (hf : v.ord f ≠ 0) :
    v.ordDiff (KaehlerDifferential.D K F f) = v.ord f - 1 := by
  revert K F x v f hf
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one.solution
