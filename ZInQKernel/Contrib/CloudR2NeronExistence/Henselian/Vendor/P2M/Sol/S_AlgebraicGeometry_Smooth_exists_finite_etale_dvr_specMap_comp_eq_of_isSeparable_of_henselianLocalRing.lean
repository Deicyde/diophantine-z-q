import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing.lean
Original Git blob: 3e7814be40ad2199c5db0419387eea53bd91e73f
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_HenselianLocalRing_of_moduleFinite_of_isLocalRing
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (k' : Type u) [Field k'] [Algebra (IsLocalRing.ResidueField R) k']
    [FiniteDimensional (IsLocalRing.ResidueField R) k'] [Algebra.IsSeparable (IsLocalRing.ResidueField R) k']
    (x₀ : Spec (CommRingCat.of k') ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField R) k').comp (IsLocalRing.residue R)))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : HenselianLocalRing R')
      (φ : k' ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R')
      (s : Spec (CommRingCat.of R') ⟶ X),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫ s =
        Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀ := by
  obtain ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, hmap, ⟨φ⟩⟩ :=
    IsDiscreteValuationRing.exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv R k'
  haveI i9 : HenselianLocalRing R' := HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R) (S := R')

  have hring : (algebraMap R' (IsLocalRing.ResidueField R')).comp (algebraMap R R') =
      φ.toRingEquiv.toRingHom.comp ((algebraMap (IsLocalRing.ResidueField R) k').comp (IsLocalRing.residue R)) := by
    ext r
    show algebraMap R' (IsLocalRing.ResidueField R') (algebraMap R R' r) =
      φ (algebraMap (IsLocalRing.ResidueField R) k' (IsLocalRing.residue R r))
    rw [AlgEquiv.commutes, IsLocalRing.ResidueField.algebraMap_residue]
    rfl
  have hcomm : (Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, hx₀, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hring]
  have hx₀' : pullback.lift _ _ hcomm ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) := pullback.lift_snd _ _ _

  obtain ⟨s', hs'₁, hs'₂⟩ :=
    AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) _ hx₀'
  have h₁ : (s' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs'₁, Category.id_comp]
  have h₂ : Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R'))) ≫
      (s' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) =
        Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ x₀ := by
    rw [← Category.assoc, hs'₂]
    exact pullback.lift_fst _ _ _
  exact ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, i9, φ, _, hmap, h₁, h₂⟩


end P2MW.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
