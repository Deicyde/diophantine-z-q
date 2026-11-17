/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport (git blob 4275977fbab11df16ecebe8c806af0d69c4da8df, sha256 4e88c95a2ba215671b717e0d8b77f9950c85e8623379a8a8d32f80b4704e94b0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm

theorem AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing F))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing F))) [μ.IsHaarMeasure]
    (fa g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) (hg : Continuous g) (hgs : HasCompactSupport g) :
    IsArchTestFactor F (fun x => ∫ a, fa (x * a) * g a ∂μ) := by
  revert F μ fa g hfa hg hgs
  exact @_root_.P2MW.S_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport.solution
