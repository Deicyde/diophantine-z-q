/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow (git blob d431ce407d6bb30edbdfd89892ee2cda6fe699bf, sha256 f23a12b49d08481514c93f0af812458b103dccf881212c186622b6f63c2591a0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField

theorem RatIdele.exists_norm_apply_eq_ideleNorm_rpow
    (μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 ℚ) ℚ μ) (hc : Continuous μ) :
    ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((μ x : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm ℚ x ^ σ := by
  revert μ hμ hc
  exact @_root_.P2MW.S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.solution
