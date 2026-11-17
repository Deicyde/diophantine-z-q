/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul (git blob 24c98f43ac9900dbb3d20f7242da5ee333ac68d6, sha256 86ad355213622cacb650fcfc4c6a6d4eca7f1690c57665b176e9c2c875aac1df).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemilinearAut.pic0_correspondence_swap_smul {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F}
    {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    (h₁ : ∀ x : F, g' • (φ x) = ψ (g • x)) (h₂ : ∀ x : F, g' • (ψ x) = φ (g • x))
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ (g • c)
      = g • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ c := by
  revert K F F' g g' φ ψ hφ hψ hFIφ hfinψ hNψ hFIψ hfinφ hNφ h₁ h₂ c
  exact @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul.solution
