/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow (git blob f37fd1bc4805255943288100a5e1d04c98f99aa0, sha256 2ff8dc4bf66775fde57150d096be36151877fb17b3b11faf799275d2dc39764d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField

theorem NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ) (hc : Continuous μ) :
    ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 K) K)ˣ, ‖((μ x : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K x ^ σ := by
  revert K μ hμ hc
  exact @_root_.P2MW.S_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.solution
