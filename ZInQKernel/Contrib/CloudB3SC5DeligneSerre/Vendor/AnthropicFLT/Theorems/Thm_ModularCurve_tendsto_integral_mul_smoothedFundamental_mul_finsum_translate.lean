/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate (git blob 46e77669cca4a684c3c189010db89d825316265f, sha256 8abdddb4a09f9e06e4ce11d51f672cfb0980fe5c95a30b86cbe0bde08f2346e7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SmoothedFundamental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.tendsto_integral_mul_smoothedFundamental_mul_finsum_translate
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℂ → ℂ) (hF : Continuous F) (hFs : HasCompactSupport F)
    (hFU : tsupport F ⊆ {z : ℂ | 0 < z.im})
    (g : ℍ → ℂ) (hg : Continuous g)
    (hgw : ∀ γ ∈ Γ, ∀ τ : ℍ, g (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * g τ)
    (h : ℝ → ℂ → ℂ) (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :
    (∀ T : ℝ, Integrable fun z : ℂ => g (ofComplex z) * h T z *
        ∑ᶠ γ : Γ, F (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
          conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2)) ∧
    Tendsto (fun T : ℝ => ∫ z : ℂ, g (ofComplex z) * h T z *
        ∑ᶠ γ : Γ, F (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
          conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2)) atTop
      (𝓝 (∫ z : ℂ, g (ofComplex z) * F z)) := by
  revert Γ F hF hFs hFU g hg hgw h hh
  exact @_root_.P2MW.S_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate.solution
