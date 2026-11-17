/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul (git blob d20cd8ee8d0bf89b017d4b41b81e938b2aa82b05, sha256 c682127b49b33edfe8bbe805c39385f5fa73f1a1189944a336bc537cb559aa64).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open NumberField NumberField.AdelicHaar AutomorphicForm MeasureTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hφ : Continuous φ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    ‖rightConv K φ f g‖ ≤
      (eLpNorm f 2 (adelicGLHaar (Fin 2) (𝓞 K) K)).toReal *
        (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict ((fun x => g * x) '' tsupport f))).toReal := by
  revert K φ f hφ hf hfs g
  exact @_root_.P2MW.S_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul.solution
