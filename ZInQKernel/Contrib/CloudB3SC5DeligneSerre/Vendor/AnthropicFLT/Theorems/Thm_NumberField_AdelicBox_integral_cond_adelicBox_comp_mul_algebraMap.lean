/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap (git blob 25be59d68b81d09f4555905e5c09c894b97db092, sha256 228992c55ff13dc4dbecf6cdbca6a74ce9bb5ea572cb39a28dc19b93a740948d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel
theorem NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap
    (F : Type) [Field F] [NumberField F]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F), f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x)
    (a : F) (ha : a ≠ 0) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) a * x)
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F))
      = ∫ x, f x ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) := by
  revert F E f hf a ha
  exact @_root_.P2MW.S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap.solution
