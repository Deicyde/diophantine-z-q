/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord (git blob b48ea15468ce9572d2b47af1e14698e48319807b, sha256 722792e5e4da4062b57380646af14b9974fcfbbfe6627e2e0ef49a1dc30bdda6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] (w : Place K F') (v : Place K F) (hv : v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F')) : ∃ e : ℕ, 0 < e ∧ ∀ f : F, w.ord (algebraMap F F' f) = e * v.ord f := by
  revert K F F' w v hv
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord.solution
