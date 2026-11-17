/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset (git blob da8480d74103de5e4e9f50d082d5d45d2d531913, sha256 2ac3b90b460c54466fa09c6818853c0be10c6e850238452088d136b33c6b0f4a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_forall_ord_eq_finset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.Place.exists_forall_ord_eq_finset {K F : Type*} [Field K] [Field F] [Algebra K F] (S : Finset (AlgebraicCurve.Place K F)) (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ g : F, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v := by
  revert K F S n
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_forall_ord_eq_finset.solution
