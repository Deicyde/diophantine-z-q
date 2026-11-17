import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension.lean
Original Git blob: a5cf3d54f45560946e73b9f0fb82692901eb2924
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    Scheme.Modules.IsLocallyFreeOfRank d (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f) ∧
      Scheme.Modules.IsLocallyFreeOfRank 1 ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d) := by
  have h1 : Scheme.Modules.IsLocallyFreeOfRank d (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, e, he⟩ :=
      AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension f d x
    exact ⟨U, hxU, AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f) U e
        (AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f) e he)⟩
  refine ⟨h1, ?_⟩
  unfold AlgebraicGeometry.Scheme.Hom.topDifferentials
  exact (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr
    (AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h1)


end P2MW.S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
