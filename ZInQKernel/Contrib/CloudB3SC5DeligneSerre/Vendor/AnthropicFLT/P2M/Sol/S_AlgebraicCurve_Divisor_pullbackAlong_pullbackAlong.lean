/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong (git blob 28b98ced1afd5a9d6591d66cd8693748e5dd35ce, sha256 0df4cc7fe6280710d67f3ff8c376978be02062e1bc77dccdc8fd3abd16697c57).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F''] (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F) : Divisor.pullbackAlong χ hχ (Divisor.pullbackAlong φ hφ D) = Divisor.pullbackAlong (χ.comp φ) hχφ D := by
  ext W
  rw [Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply,
    AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
    AlgebraicCurve.Place.ramificationIndexAlong_comp φ χ hφ hχ hχφ]
  push_cast
  ring
