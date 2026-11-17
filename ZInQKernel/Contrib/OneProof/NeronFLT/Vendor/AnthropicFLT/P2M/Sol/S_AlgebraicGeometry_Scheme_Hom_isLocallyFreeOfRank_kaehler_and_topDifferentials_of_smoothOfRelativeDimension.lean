/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    Scheme.Modules.IsLocallyFreeOfRank d f.kaehler ∧
      Scheme.Modules.IsLocallyFreeOfRank 1 (f.topDifferentials d) := by
  have h1 : Scheme.Modules.IsLocallyFreeOfRank d f.kaehler := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, e, he⟩ :=
      AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension f d x
    exact ⟨U, hxU, AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis
      f.kaehler U e
        (AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen f.kaehler e he)⟩
  refine ⟨h1, ?_⟩
  unfold AlgebraicGeometry.Scheme.Hom.topDifferentials
  exact (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr
    (AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h1)
