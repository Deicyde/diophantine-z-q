/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg (git blob 48ee8eb6d92cb382c67a426d08195548147dfd12, sha256 22581d11e5f2808fefe1b7b5db28c3a26a0b1f29032d17dcc7c62a6a72d89a14).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (t : F) (ht : Transcendental K t) [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] [AlgebraicCurve.HasPrincipalDivisors K F] (z : F) (hz : ∀ v : AlgebraicCurve.Place K F, 0 ≤ v.ord t → 0 ≤ v.ord z) : IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by
  revert K F t ht z hz
  exact @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.solution
