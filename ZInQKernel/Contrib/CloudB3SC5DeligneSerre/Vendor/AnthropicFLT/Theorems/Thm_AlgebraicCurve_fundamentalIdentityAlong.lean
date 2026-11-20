/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong (git blob 39a531a418d12611aef26316434857a385385c50, sha256 497b32a94e52a10d0905358ebe4b583c1e12fa2d9bc9d2d2a953ce0e1ab91d65).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_fundamentalIdentityAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.fundamentalIdentityAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) [HasPrincipalDivisors K F'] (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) : FundamentalIdentityAlong K φ hφ := by
  revert K F F' φ hφ hfin hsep
  exact @_root_.P2MW.S_AlgebraicCurve_fundamentalIdentityAlong.solution
