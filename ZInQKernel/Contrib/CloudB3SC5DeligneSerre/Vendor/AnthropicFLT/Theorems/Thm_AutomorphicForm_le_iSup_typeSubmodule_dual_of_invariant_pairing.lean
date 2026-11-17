/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing (git blob 73972945371624cd546ba7c1276d53a87780ec29, sha256 95cbc01be8c7da1dcabbbf21924592690e2871510b8a10292d708915d2295873).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.le_iSup_typeSubmodule_dual_of_invariant_pairing
    {K : Type*} [Group K] {G : Type*} [Group G]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ}
    (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i))
    (S T : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k : K, ∀ s ∈ S, (fun x => s (x * ι k)) ∈ S) (hT : ∀ k : K, ∀ t ∈ T, (fun x => t (x * ι k)) ∈ T)
    (β : S →ₗ[ℂ] T →ₗ[ℂ] ℂ)
    (hβ : ∀ (k : K) (s : S) (t : T), β ⟨fun x => (s : G → ℂ) (x * ι k), hS k s s.2⟩ ⟨fun x => (t : G → ℂ) (x * ι k), hT k t t.2⟩ = β s t)
    (hnd : ∀ t : T, (∀ s : S, β s t = 0) → t = 0)
    (hSle : S ≤ ⨆ i, typeSubmodule ι (ρ i)) :
    T ≤ ⨆ i, typeSubmodule ι (ρ i).dual := by
  revert K G ι hι n W ρ S T hS hT β hβ hnd hSle
  exact @_root_.P2MW.S_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing.solution
