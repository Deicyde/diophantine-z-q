/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact (git blob 8bb0d58e6c411b2d79b9c7e5fb938fa2c0595c5a, sha256 9cb58cdc7fea673fc5cd97cf60a41d1828a4db76a1e6ef756baf20dc34a45732).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact

open NumberField FLT.SmoothVectors AutomorphicForm

namespace Rho7aSol

theorem IsSmoothVector.finite_smul_image_of_isCompact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type*} [MulAction G M] {v : M} (hv : IsSmoothVector G v)
    {K : Set G} (hK : IsCompact K) : Set.Finite ((· • v) '' K) := by
  set U := MulAction.stabilizer G v
  have hUo : IsOpen (U : Set G) := hv

  have hcov : K ⊆ ⋃ k ∈ K, (fun g => k * g) '' (U : Set G) := by
    intro k hk
    simp only [Set.mem_iUnion]
    exact ⟨k, hk, 1, Subgroup.one_mem U, mul_one k⟩
  have hopen : ∀ k ∈ K, IsOpen ((fun g => k * g) '' (U : Set G)) := by
    intro k _
    exact (Homeomorph.mulLeft k).isOpenMap _ hUo
  obtain ⟨t, _htK, htF, htcov⟩ := hK.elim_finite_subcover_image hopen hcov
  refine (htF.image (· • v)).subset (fun w hw => ?_)
  simp only [Set.mem_image] at hw ⊢
  obtain ⟨k, hkK, rfl⟩ := hw
  have hk := htcov hkK
  simp only [Set.mem_iUnion, Set.mem_image] at hk
  obtain ⟨j, hjT, u, huU, hju⟩ := hk
  exact ⟨j, hjT, by rw [← hju, mul_smul, MulAction.mem_stabilizer_iff.mp huU]⟩

end Rho7aSol

theorem solution {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) {K : Set ↥(finiteAdelicGL2Subgroup F)} (hK : IsCompact K) :
    Set.Finite ((· • (RightTranslationFn.mk φ :
      RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) '' K) :=
  Rho7aSol.IsSmoothVector.finite_smul_image_of_isCompact hφ hK

#print axioms solution
