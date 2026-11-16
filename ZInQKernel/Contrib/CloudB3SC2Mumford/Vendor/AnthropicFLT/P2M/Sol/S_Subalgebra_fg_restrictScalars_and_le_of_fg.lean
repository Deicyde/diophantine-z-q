/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Subalgebra_fg_restrictScalars_and_le_of_fg
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

namespace P2MW.S_Subalgebra_fg_restrictScalars_and_le_of_fg

set_option autoImplicit false

universe u

theorem solution
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (T : Subalgebra A₀ A) (hT : T.FG) (T' : Subalgebra ↥T A) (hT' : T'.FG) :
    (T'.restrictScalars A₀).FG ∧ (T : Set A) ⊆ (T'.restrictScalars A₀ : Set A) := by
  classical
  obtain ⟨s, rfl⟩ := hT
  obtain ⟨t, rfl⟩ := hT'
  have key : (Algebra.adjoin (↥(Algebra.adjoin A₀ (↑s : Set A))) (↑t : Set A)).restrictScalars A₀ =
      Algebra.adjoin A₀ ((↑s : Set A) ∪ ↑t) :=
    (Algebra.adjoin_union_eq_adjoin_adjoin A₀ (↑s : Set A) ↑t).symm
  refine ⟨⟨s ∪ t, ?_⟩, ?_⟩
  · rw [key, Finset.coe_union]
  · rw [key]
    exact Algebra.adjoin_mono Set.subset_union_left
