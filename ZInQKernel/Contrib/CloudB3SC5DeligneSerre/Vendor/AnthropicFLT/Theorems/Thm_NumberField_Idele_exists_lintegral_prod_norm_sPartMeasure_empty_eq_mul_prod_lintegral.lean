/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral (git blob 2e3968d4d273ddf9bf02e55ecff393c51cefcdff, sha256 258d4bb4414e0acacd7e35be5c319b6eddf742e41dadb092d248b2e0dd06c754).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_IdeleProductMeasure
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.Idele MeasureTheory
open scoped ENNReal

theorem NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral
    (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ h : InfinitePlace F → ℝ → ℝ≥0∞, (∀ w, Measurable (h w)) →
        (∫⁻ a, ∏ w : InfinitePlace F, h w ‖((a : AdeleRing (𝓞 F) F).1 w)‖ ∂(sPartMeasure F ∅)) =
          C * ∏ w : InfinitePlace F, ∫⁻ t in Set.Ioi (0 : ℝ), h w t * (ENNReal.ofReal t)⁻¹ := by
  revert F
  exact @_root_.P2MW.S_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral.solution
