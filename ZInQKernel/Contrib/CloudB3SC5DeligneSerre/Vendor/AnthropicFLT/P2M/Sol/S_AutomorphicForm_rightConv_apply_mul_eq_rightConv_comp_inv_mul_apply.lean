/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply (git blob 623878eb9f0ca0c098ae7d45690cc3f18ae30ef5, sha256 643b26ffcc053b9da5d0e7e69347f99cb5125d005a08db3c515484c2ea060be2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply

open NumberField
open MeasureTheory AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f (g * t) = rightConv K φ (fun y => f (t⁻¹ * y)) g := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  show (∫ x, φ (g * t * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      = ∫ x, φ (g * x) * f (t⁻¹ * x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  have h := integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun x => φ (g * x) * f (t⁻¹ * x)) t
  simp only [inv_mul_cancel_left] at h
  simpa only [mul_assoc] using h
