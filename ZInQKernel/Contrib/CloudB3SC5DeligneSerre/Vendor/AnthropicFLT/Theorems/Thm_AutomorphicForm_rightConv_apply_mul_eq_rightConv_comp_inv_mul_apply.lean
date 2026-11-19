/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply (git blob b06beff66267b283e2338bff0c4f773856761733, sha256 a80c6d564f31f2866d2f11d273f3c524429a7cfc43a398cd1f65ad74086a5807).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField

theorem AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f (g * t) = rightConv K φ (fun y => f (t⁻¹ * y)) g := by
  revert K φ f g t
  exact @_root_.P2MW.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply.solution
