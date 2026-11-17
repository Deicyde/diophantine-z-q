/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv (git blob 5d721c3b6a3a0d5227e93351b34cdf66711b91ee, sha256 6aa77f394cacb649c765751b0cf55d124d2d3672e1283cd6d67c4b77d757a2b3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm

theorem AutomorphicForm.rightConv_rightConv_eq_rightConv_rightConv_comp_inv
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (f h : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    rightConv F (rightConv F φ f) h = rightConv F φ (rightConv F h fun x => f x⁻¹) := by
  revert F φ hφ f h hfc hfs hhc hhs
  exact @_root_.P2MW.S_AutomorphicForm_rightConv_rightConv_eq_rightConv_rightConv_comp_inv.solution
