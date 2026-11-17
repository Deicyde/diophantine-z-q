/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute (git blob eba829798335659835b4741843c9cc626f0805ff, sha256 e97c1db24d3e720b44bc3ec1541e2e0702da61dfcb3504ab28e0815c6ae664e6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ContinuousLinearMap_map_eigenspace_orthogonal_le_of_commute

set_option autoImplicit false

open Module.End
open scoped InnerProductSpace

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    (S : E →L[𝕜] E) (hST : S.comp T = T.comp S) (μ : 𝕜) (hμ : μ ≠ 0) :
    (eigenspace (T : Module.End 𝕜 E) μ).map (S : Module.End 𝕜 E) ≤ eigenspace (T : Module.End 𝕜 E) μ ∧
    ((eigenspace (T : Module.End 𝕜 E) μ)ᗮ).map (S : Module.End 𝕜 E) ≤ (eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by

  have hTsa : IsSelfAdjoint T := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hT'
  have hadj : ContinuousLinearMap.adjoint T = T := hTsa.adjoint_eq
  have hST' : (ContinuousLinearMap.adjoint S).comp T = T.comp (ContinuousLinearMap.adjoint S) := by
    have h := congrArg ContinuousLinearMap.adjoint hST
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hadj] at h
    exact h.symm

  have hpres : ∀ R : E →L[𝕜] E, R.comp T = T.comp R →
      ∀ v ∈ eigenspace (T : Module.End 𝕜 E) μ, R v ∈ eigenspace (T : Module.End 𝕜 E) μ := by
    intro R hR v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : T v = μ • v := hv
    show T (R v) = μ • R v
    have h := congrArg (fun f : E →L[𝕜] E => f v) hR
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h, hv', map_smul]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hpres S hST v hv
  · rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro e he
    show ⟪e, S v⟫_𝕜 = 0
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).mp hv _ (hpres _ hST' e he)
