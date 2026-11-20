/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ord_eq_zero_of_isIntegral_adjoin (git blob 81fb965f2ad8a29ae99bf0d36fc81b638e706c3c, sha256 32fb77cdead369972ec97ea91f34b57b4f3577c44cbd5632a2779095bfbb4070).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_ord_eq_zero_of_isIntegral_adjoin

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring) (hx : IsIntegral (Algebra.adjoin K {j}) x) (hx' : IsIntegral (Algebra.adjoin K {j}) x⁻¹) : v.ord x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact v.ord_zero
  · have hxa : x ∈ v.toValuationSubring :=
      v.mem_toValuationSubring_of_isIntegral_adjoin hj hx
    have hxi : x⁻¹ ∈ v.toValuationSubring :=
      v.mem_toValuationSubring_of_isIntegral_adjoin hj hx'
    have hunit : IsUnit (⟨x, hxa⟩ : v.toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hxi⟩, ?_⟩
      ext
      simp [mul_inv_cancel₀ hx0]
    have h1 : v.adicValuation x = 1 :=
      (v.adicValuation_coe_eq_one_iff ⟨x, hxa⟩).mpr hunit
    simp [AlgebraicCurve.Place.ord, h1]
