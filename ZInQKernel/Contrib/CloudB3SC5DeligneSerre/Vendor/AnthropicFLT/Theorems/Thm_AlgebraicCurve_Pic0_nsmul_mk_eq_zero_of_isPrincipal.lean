/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal (git blob 49561c6045e0fd88bfa88c993928f3421f21e2c6, sha256 f74ba777eb4b54ec5f54abf9ed111e4c7b08ae5cc84b5c1f4e13fbfdfd71fc69).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.nsmul_mk_eq_zero_of_isPrincipal {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by
  revert K F D m hD
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal.solution
