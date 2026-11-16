/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (T : Closeds X) (hT : Set.range i.base = (T : Set X))
    (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ T' : Closeds X, T' < T ∧ ∀ z : Z, z ∉ U → i.base z ∈ T' := by
  have hce : Topology.IsClosedEmbedding i.base := i.isClosedEmbedding
  refine ⟨⟨i.base '' ((U : Set Z)ᶜ), hce.isClosedMap _ U.isOpen.isClosed_compl⟩, ?_, fun z hz => ⟨z, hz, rfl⟩⟩
  rw [SetLike.lt_iff_le_and_exists]
  obtain ⟨u, hu⟩ := hU
  refine ⟨?_, i.base u, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, -, rfl⟩ := (Closeds.mem_mk).mp hx
    have : i.base z ∈ (T : Set X) := hT ▸ ⟨z, rfl⟩
    exact this
  · have : i.base u ∈ (T : Set X) := hT ▸ ⟨u, rfl⟩
    exact this
  · intro h
    obtain ⟨z, hz, hzu⟩ := (Closeds.mem_mk).mp h
    exact hz (by rwa [hce.injective hzu])
