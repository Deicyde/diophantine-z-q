import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed.lean
Original Git blob: 8daf9ba6da35c5096d1f9974d79cb92048c8b966
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (Y : Set X) (hY : IsClosed Y) (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R) :
    ∃ (D : Scheme.{u}) (p : D ⟶ X),
      IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ W : X.Opens, (∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) → IsIso (p ∣_ W)) ∧
      (∀ d : D, f (p d) = IsLocalRing.closedPoint R → p d ∈ Y) ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (π : R),
        IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ e : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π))))),
          (p ⁻¹ᵁ U).ι ≫ p = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫ hU.fromSpec) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
