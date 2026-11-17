/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower (git blob 5c64f863d1425c4b1e1745b794a3f41bfa21d5f4, sha256 082d21b964f81a8874a606aeccf6ca3caa93376827c9067a683f28c40e368366).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.isIntegral_adjoin_of_isScalarTower {K L F : Type*} [CommRing K] [CommRing L] [CommRing F] [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] {j x : F} (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin L {j}) x := by
  revert K L F j x hx
  exact @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower.solution
