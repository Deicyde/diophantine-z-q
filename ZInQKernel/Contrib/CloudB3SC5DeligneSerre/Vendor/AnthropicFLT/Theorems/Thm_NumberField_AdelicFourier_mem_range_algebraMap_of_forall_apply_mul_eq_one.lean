/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one (git blob 74da4c6525ba1d834b0cbc944982a140568fa5cb, sha256 a1f847d9cac437c1c3f46511db496b890c9d950bad5e6d11c49e3215382b1e25).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField AutomorphicForm
theorem NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (y : AdeleRing (𝓞 F) F)
    (hy : ∀ ξ : F, ψ (y * algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1) :
    y ∈ Set.range (algebraMap F (AdeleRing (𝓞 F) F)) := by
  revert F ψ hψ y hy
  exact @_root_.P2MW.S_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one.solution
