/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective (git blob 8fbe01049005a4d9c3f7e8be98154679090d9353, sha256 5b420cee4c7cc0874ed0b9e51398c584466275763f0481a5226d3293a51e2928).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective
    {H G : Type*} [Group H] [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H W)
    (A : Submodule ℂ W) (hA : ∀ (k : H) (a : W), a ∈ A → ρ k a ∈ A)
    (TA : ↥A →ₗ[ℂ] (G → ℂ))
    (hTA : ∀ (k : H) (a : ↥A) (x : G), TA ⟨ρ k a, hA k a a.2⟩ x = TA a (x * ι k)) :
    ∃ T : W →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ T ∧ T ∘ₗ A.subtype = TA := by
  revert H G W ι hι ρ A hA TA hTA
  exact @_root_.P2MW.S_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective.solution
