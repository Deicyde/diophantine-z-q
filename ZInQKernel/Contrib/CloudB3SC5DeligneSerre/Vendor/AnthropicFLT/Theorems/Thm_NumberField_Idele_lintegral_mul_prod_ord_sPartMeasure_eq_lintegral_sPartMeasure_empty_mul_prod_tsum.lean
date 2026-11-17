/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum (git blob 565b8786dba987cdf5c928353a289e9aac94e488, sha256 ec66996ab38437c65db29a53a8bf53a16e1059172de2ca9fa1b505d4ad897a95).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_IdeleProductMeasure
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.Idele IsDedekindDomain
open scoped ENNReal

theorem NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable[ideleBorel F] f)
    (hf1 : ∀ a b : (AdeleRing (𝓞 F) F)ˣ, ((a : AdeleRing (𝓞 F) F)).1 = ((b : AdeleRing (𝓞 F) F)).1 → f a = f b)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) :
    (∫⁻ a, f a * ∏ v ∈ S, φ v (ord F v a) ∂(sPartMeasure F S)) =
      (∫⁻ a, f a ∂(sPartMeasure F ∅)) * ∏ v ∈ S, ∑' m : ℤ, φ v m := by
  revert F S f hf hf1 φ
  exact @_root_.P2MW.S_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum.solution
