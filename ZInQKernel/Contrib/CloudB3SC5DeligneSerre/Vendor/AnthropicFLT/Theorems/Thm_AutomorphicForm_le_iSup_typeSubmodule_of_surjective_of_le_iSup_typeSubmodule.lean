/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule (git blob 6ba02a96bba8c6b64bc6a0a259b5a62048e4f0e6, sha256 2c572f1557ab00bb9ee1c136a38eafa7b6c871ca4e8c35d07f50442980c91a2f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule
    {K : Type*} [Group K] {G : Type*} [Group G]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ}
    (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i))
    (S S' : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ S]
    (hS' : ∀ k : K, ∀ s ∈ S', (fun x => s (x * ι k)) ∈ S')
    (hS : ∀ k : K, ∀ s ∈ S, (fun x => s (x * ι k)) ∈ S)
    (θ : S →ₗ[ℂ] S') (hθs : Function.Surjective θ)
    (hθ : ∀ (k : K) (s : S),
      (θ ⟨fun x => (s : G → ℂ) (x * ι k), hS k s s.2⟩ : G → ℂ) = fun x => (θ s : G → ℂ) (x * ι k))
    (hSA : S ≤ ⨆ i, typeSubmodule ι (ρ i)) :
    S' ≤ ⨆ i, typeSubmodule ι (ρ i) := by
  revert K G ι hι n W ρ S S' hS' hS θ hθs hθ hSA
  exact @_root_.P2MW.S_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule.solution
