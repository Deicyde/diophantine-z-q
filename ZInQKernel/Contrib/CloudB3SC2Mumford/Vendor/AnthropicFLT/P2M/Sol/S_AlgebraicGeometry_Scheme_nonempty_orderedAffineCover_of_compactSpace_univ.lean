/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    (X : Scheme.{u}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  letI : LinearOrder ↥t := LinearOrder.lift' (Fintype.equivFin ↥t) (Fintype.equivFin ↥t).injective
  refine ⟨{ ι := ↥t, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨U, hUt, hxU⟩ := hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩
