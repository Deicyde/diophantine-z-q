import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes.lean
Original Git blob: 5434022fc6a2a9a12065306049e297cb9cb8bf80
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hgen : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ)
    [Algebra R (Z.presheaf.stalk ζ)]
    (halg : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ)))) :
    ∃ (_ : IsDomain (Z.presheaf.stalk ζ)) (_ : IsDiscreteValuationRing (Z.presheaf.stalk ζ))
      (_ : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ))),
      IsIndexOneExtension R (Z.presheaf.stalk ζ) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
