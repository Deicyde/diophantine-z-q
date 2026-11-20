/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne (git blob f44dc98ab1e77c69f8efb0f5bc376e1c85517b35, sha256 95a5dde1b8c23a0c7722a459e390b89a66f8abe5abcdd9b92d2d3f364f35f0f8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem Matrix.SpecialLinearGroup.exists_generators_free_mod_neg_one_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    ∃ gens : Fin (1 + Γ.index / 6) → Γ,
      Subgroup.closure (Set.range gens ∪ {⟨-1, hneg⟩}) = ⊤ ∧
      ∀ (L : Type) [Group L] (v : Fin (1 + Γ.index / 6) → L),
        ∃ f : Γ →* L, ∀ i, f (gens i) = v i := by
  revert Γ hneg hΓ
  exact @_root_.P2MW.S_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne.solution
