/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_RightConvolution (git blob 8a59e1c6df29222a35545f6082187f1990cc9ee1, sha256 8bd5406d4a982a7b0b68857891e046449048c00e0be3c3a2bda8840f8a7465d1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField

namespace AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

noncomputable def rightConv (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ :=
  fun g =>
    (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
     ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))

theorem rightConv_apply (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f g =
      (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
       ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) :=
  rfl

theorem rightConv_zero_right (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K φ (fun _ => 0) = fun _ => 0 := by
  funext g
  simp [rightConv]

theorem rightConv_zero_left (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K (fun _ => 0) f = fun _ => 0 := by
  funext g
  simp [rightConv]

theorem rightConv_comp_mul_left (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (h g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K (fun x => φ (h * x)) f g = rightConv K φ f (h * g) := by
  simp only [rightConv, mul_assoc]

end AutomorphicForm
