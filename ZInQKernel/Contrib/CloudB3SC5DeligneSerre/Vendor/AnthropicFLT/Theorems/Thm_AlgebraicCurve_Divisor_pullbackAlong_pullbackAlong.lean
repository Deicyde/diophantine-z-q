/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong (git blob 60d6aa29230ad7915cbaecc1f69616e5fece7cf5, sha256 f6ef5cc5934da158adc378544b8477888c637d0f84e94fc8369d9bf369b4290f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F''] (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F) : Divisor.pullbackAlong χ hχ (Divisor.pullbackAlong φ hφ D) = Divisor.pullbackAlong (χ.comp φ) hχφ D := by
  revert K F F' F'' φ χ hφ hχ hχφ D
  exact @_root_.P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong.solution
