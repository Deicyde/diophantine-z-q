/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg (git blob c20ffe6344b960a1f62a0e3e9e45987a62fe1bc0, sha256 1b381b32280d6bdcb3253207c0c00c30efdc157c1f51fe94b1ac8a54d3075a88).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_mem
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_iff_ord_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve.Place
end AlgebraicCurve.Place
namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place)
namespace Place
export _root_.AlgebraicCurve.Place (mem_toValuationSubring_of_isIntegral_adjoin ord toValuationSubring ord_nonneg_of_mem mem_iff_ord_nonneg)
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

private theorem ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg_impl {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {j u : F} (hu : IsIntegral (Algebra.adjoin K {j}) u) (hj : 0 ≤ v.ord j) :
    0 ≤ v.ord u := by
  have hjmem : j ∈ v.toValuationSubring := by
    rcases eq_or_ne j 0 with rfl | hj0
    · exact zero_mem _
    · exact (v.mem_iff_ord_nonneg hj0).mpr hj
  exact v.ord_nonneg_of_mem (v.mem_toValuationSubring_of_isIntegral_adjoin hjmem hu)

end AlgebraicCurve.Place

theorem solution {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : AlgebraicCurve.Place K F) {j u : F} (hu : IsIntegral (Algebra.adjoin K {j}) u)
    (hj : 0 ≤ v.ord j) : 0 ≤ v.ord u :=
  AlgebraicCurve.Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg_impl v hu hj
