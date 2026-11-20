/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero (git blob b4d98c3d5d59b200e14f3a1e3dc1686b1ca506ff, sha256 87c8dfccf7a0424c97503fad75f15af1c070fa4d9164b76c6616f517af5b47c6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ord_smul_of_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Place.ord_smul_of_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  revert K F v c hc x
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ord_smul_of_ne_zero.solution
