import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing.lean
Original Git blob: f003cb224b82cd3cd5c7f6e983da8e715e386743
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens) (hU₁ : IsAffineOpen U)
    (hU₂ : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ V : B.Opens, IsAffineOpen V ∧ ∀ b ∈ S, b ∈ V := by
  classical

  obtain ⟨Z, ⟨z, hzZ, hz⟩, hZ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_forall_mul_base_mem_of_forall_specializes_mem
      LB U hU₂ S

  obtain ⟨R', _instCR, _instDom, _instDVR, _instAlg, _instFin, _instEt, _instFF, _instLoc, _instHens, a,
      _hmap, ha, haZ⟩ :=
    AlgebraicGeometry.Smooth.exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
      g Z z hz hzZ

  have hz' : g.base (a.base (IsLocalRing.closedPoint R')) = IsLocalRing.closedPoint R := by
    have h : g.base (a.base (IsLocalRing.closedPoint R')) =
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))).base (IsLocalRing.closedPoint R') := by
      rw [← Scheme.Hom.comp_apply, ha]
    rw [h]
    show PrimeSpectrum.comap (algebraMap R R') (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R
    exact IsLocalRing.comap_closedPoint (algebraMap R R')

  have hS := hZ (a.base (IsLocalRing.closedPoint R')) haZ hz' R' a ha rfl

  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr ‹Module.Finite R R'›)
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R')⟩

  exact GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem LB
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (⟨a, ha⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g) U hU₁ S hS


end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
