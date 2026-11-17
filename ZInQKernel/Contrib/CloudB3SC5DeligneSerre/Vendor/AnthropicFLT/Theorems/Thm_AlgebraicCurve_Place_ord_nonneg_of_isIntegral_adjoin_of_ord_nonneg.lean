/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg (git blob 659922ef10f028aa1669a4b4483f3eae0fcd91f0, sha256 bd4eae6fefb3e90853898c1870a7bdfb0fc11efb13ac5ffdeece37aa1e7aeb9b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : AlgebraicCurve.Place K F) {j u : F} (hu : IsIntegral (Algebra.adjoin K {j}) u)
    (hj : 0 ≤ v.ord j) : 0 ≤ v.ord u := by
  revert K F v j u hu hj
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg.solution
