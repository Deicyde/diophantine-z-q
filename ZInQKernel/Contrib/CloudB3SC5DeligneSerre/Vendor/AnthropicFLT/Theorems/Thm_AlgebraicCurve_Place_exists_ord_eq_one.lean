/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one (git blob 943c3428bee02ea2e6e667fc0eac38d57e8d92d4, sha256 809479e7b3cd14af1f646ad2d8f541b6fdf0e6b3556ae900aa4ecc874335360d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_ord_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.Place.exists_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ t : F, v.ord t = 1 := by
  revert K F v
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one.solution
