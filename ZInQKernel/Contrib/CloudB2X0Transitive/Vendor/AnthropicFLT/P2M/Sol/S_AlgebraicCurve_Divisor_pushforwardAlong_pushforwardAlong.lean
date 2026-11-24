/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_inertiaDegAlong_comp
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F'') : Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D) = Divisor.pushforwardAlong (χ.comp φ) hχφ D := by
  have key : (Divisor.pushforwardAlong φ hφ).comp (Divisor.pushforwardAlong χ hχ)
      = Divisor.pushforwardAlong (χ.comp φ) hχφ := by
    refine Finsupp.addHom_ext fun W n => ?_
    show Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ (Finsupp.single W n))
        = Divisor.pushforwardAlong (χ.comp φ) hχφ (Finsupp.single W n)
    rw [Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single,
      AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
      AlgebraicCurve.Place.inertiaDegAlong_comp φ χ hφ hχ hχφ W]
    refine congrArg (Finsupp.single _) ?_
    push_cast
    ring
  exact DFunLike.congr_fun key D
