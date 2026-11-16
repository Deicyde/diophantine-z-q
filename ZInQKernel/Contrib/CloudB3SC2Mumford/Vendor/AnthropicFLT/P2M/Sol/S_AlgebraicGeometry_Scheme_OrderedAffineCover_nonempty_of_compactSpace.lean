/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

theorem solution (V : Scheme.{u}) [CompactSpace V] : Nonempty V.OrderedAffineCover := by

  have hcov_all : (Set.univ : Set V) ⊆ ⋃ W : V.affineOpens, (W.1 : Set V) := fun x _ => by
    obtain ⟨W, hWaff, hxW, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.isBasis_affineOpens
        (show x ∈ (⊤ : V.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨W, hWaff⟩, hxW⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun W : V.affineOpens => (W.1 : Set V))
    (fun W => W.1.2) hcov_all

  letI _lo : LinearOrder V.affineOpens := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨{ ι := S, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine le_antisymm le_top (fun x _ => ?_)
  rcases Set.mem_iUnion₂.mp (hS (Set.mem_univ x)) with ⟨W, hWS, hxW⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWS⟩, hxW⟩
