/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant (git blob 765f73460512a9a4c5a112cbe4887279298f37d4, sha256 44f5d7e626d78a2528a2538c27b8830a8f7eeab4c6b653f56a3866fa75dce48a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_IdeleProductMeasure
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant

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

theorem AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
    (K : Type) [Field K] [NumberField K]
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        ∫⁻ b, F (b : AdelicGL2 (𝓞 K) K) ∂μB =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t,
                F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K) := by
  revert K μB
  exact @_root_.P2MW.S_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.solution
