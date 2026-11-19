/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure (git blob 40e1a689390aefce6c3eee50dbf15b8e6bb02a2a, sha256 860a5c9580efb9efbae0f405f0d39375d22c5198baea4f34e0d3cf2ec8320174).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_IdeleProductMeasure
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_M4aHerbrand_IdeleClassVocab
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure
    (K : Type) [Field K] [NumberField K] (c : ℝ≥0∞)
    (hc : ∀ (D : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
      ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalCentreUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
                f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hfH : ∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ q in {q : RationalCentreUnipotentQuotient K | q.out ∈ RankinSelberg.shellZeroOutside K S},
        f q.out ∂(rationalCentreUnipotentQuotientMeasure K) =
      c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
            f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S) ∂(NumberField.Idele.idelicHaar K) := by
  revert K c hc S D hD hDF f hf hfH
  exact @_root_.P2MW.S_AutomorphicForm_setLIntegral_rationalCentreUnipotentQuotientMeasure_shellZeroOutside_eq_mul_lintegral_sPartMeasure.solution
