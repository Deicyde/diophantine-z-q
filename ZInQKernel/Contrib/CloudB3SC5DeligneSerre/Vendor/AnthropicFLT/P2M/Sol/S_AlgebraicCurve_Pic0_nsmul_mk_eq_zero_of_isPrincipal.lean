/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal (git blob 5c36c9111844e3cc080accd0a7eca203131e4899, sha256 e0b276d14e80e8c8abb59f44a027528380cab0a6462523032d08c7c16e9dbbd7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by
  have h := AlgebraicCurve.Pic0.zsmul_mk_eq_zero_of_isPrincipal D (m : ℤ) (by rwa [natCast_zsmul])
  rwa [natCast_zsmul] at h
