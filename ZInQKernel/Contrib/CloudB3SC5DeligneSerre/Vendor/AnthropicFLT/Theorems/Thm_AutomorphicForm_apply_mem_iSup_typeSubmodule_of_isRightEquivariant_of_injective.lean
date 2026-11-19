/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective (git blob 136b46045aa2a30c30b79dbb5b2cf5d1e3e4fd68, sha256 904b33e7c8caf45b23bd29e9feff80a0acfaccbee06ded460953b445f0ad2807).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
    {H K G : Type*} [Group H] [Group K] [Group G]
    (j : H →* K) (ι' : H →* G) (hι' : Function.Injective ι')
    (C : Submodule ℂ (K → ℂ)) (hC : ∀ (k : H) (u : K → ℂ), u ∈ C → (fun κ => u (κ * j k)) ∈ C)
    (A : ↥C →ₗ[ℂ] (G → ℂ))
    (hA : ∀ (k : H) (u : ↥C) (x : G),
      A ⟨fun κ => (u : K → ℂ) (κ * j k), hC k u u.2⟩ x = A u (x * ι' k))
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) (u : K → ℂ) (hu : u ∈ C)
    (hut : u ∈ ⨆ i, typeSubmodule j (ρ i)) :
    A ⟨u, hu⟩ ∈ ⨆ i, typeSubmodule ι' (ρ i) := by
  revert H K G j ι' hι' C hC A hA I W ρ u hu hut
  exact @_root_.P2MW.S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective.solution
