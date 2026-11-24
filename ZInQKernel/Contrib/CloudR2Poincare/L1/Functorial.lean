-- Ported from frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272,
-- module Jacobian.AlgebraicGeometry.Picard.Functorial, Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu.
-- See LICENSE and NOTICE in this L1 directory and in CloudW07JacobiansCurves.
-- CHANGE NOTICE (H-72 round 2, L1): imports use the existing vendored contribution;
-- all new declarations are renamed into ZInQ.Contrib.CloudR2Poincare.L1;
-- baseChangeMap refers to the vendor's AlgebraicGeometry.JacobianChallenge.baseChangeMap.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RepresentableGroup
import ZInQKernel.Contrib.CloudR2Poincare.L1.SheafifyMap

/-!
# General Picard-sheaf pullback

This port supplies the genuinely general part of the dual-map construction:
an arbitrary morphism of schemes over a base induces pullback of the relative
Picard **sheaf** and its tensor group law. It does not claim representability,
existence of a dual abelian variety, or preservation of a general Pic⁰ scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

variable {base : Scheme.{u}} {source target thirdScheme : Over base}

/-- The map of Cartesian families induced by a morphism over the base. -/
def picardFamilyMap (morphism : source ⟶ target) (parameter : Over base) :
    pullback source.hom parameter.hom ⟶ pullback target.hom parameter.hom :=
  pullback.lift (pullback.fst source.hom parameter.hom ≫ morphism.left)
    (pullback.snd source.hom parameter.hom) (by
      rw [Category.assoc, Over.w, pullback.condition])

@[simp]
theorem picardFamilyMap_id (parameter : Over base) :
    picardFamilyMap (𝟙 source) parameter = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [picardFamilyMap]

/-- Maps of families respect composition. -/
theorem picardFamilyMap_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdScheme) (parameter : Over base) :
    picardFamilyMap (firstMap ≫ secondMap) parameter =
      picardFamilyMap firstMap parameter ≫ picardFamilyMap secondMap parameter := by
  apply pullback.hom_ext <;> simp [picardFamilyMap, Category.assoc]

/-- Pullback in the family variable commutes with parameter restriction. -/
theorem picardFamilyMap_naturality (morphism : source ⟶ target)
    {parameter otherParameter : Over base} (restriction : otherParameter ⟶ parameter) :
    JacobianChallenge.baseChangeMap source.hom restriction ≫ picardFamilyMap morphism parameter =
      picardFamilyMap morphism otherParameter ≫
        JacobianChallenge.baseChangeMap target.hom restriction := by
  apply pullback.hom_ext <;>
    simp [picardFamilyMap, JacobianChallenge.baseChangeMap, Category.assoc]

/-- Actual pullback as a natural transformation of group presheaves. -/
def picardPresheafPullbackGrp (morphism : source ⟶ target) :
    picardPresheafGrp target.hom ⟶ picardPresheafGrp source.hom where
  app parameter := GrpCat.ofHom (Pic.mapHom (picardFamilyMap morphism parameter.unop))
  naturality _ _ restriction := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro picardClass
    change Pic.map (picardFamilyMap morphism _)
        (Pic.map (JacobianChallenge.baseChangeMap target.hom restriction.unop) picardClass) =
      Pic.map (JacobianChallenge.baseChangeMap source.hom restriction.unop)
        (Pic.map (picardFamilyMap morphism _) picardClass)
    rw [← Pic.map_comp, ← Pic.map_comp, picardFamilyMap_naturality]

/-- Pullback of line-bundle classes, forgetting the group law. -/
def picardPresheafPullback (morphism : source ⟶ target) :
    picardPresheaf target.hom ⟶ picardPresheaf source.hom :=
  CategoryTheory.Functor.whiskerRight (picardPresheafPullbackGrp morphism) (forget GrpCat)

@[simp]
theorem picardPresheafPullbackGrp_id :
    picardPresheafPullbackGrp (𝟙 source) = 𝟙 (picardPresheafGrp source.hom) := by
  ext parameter picardClass
  change Pic.map (picardFamilyMap (𝟙 source) parameter.unop) picardClass = picardClass
  rw [picardFamilyMap_id, Pic.map_id]

/-- Presheaf pullback is contravariant. -/
theorem picardPresheafPullbackGrp_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdScheme) :
    picardPresheafPullbackGrp (firstMap ≫ secondMap) =
      picardPresheafPullbackGrp secondMap ≫ picardPresheafPullbackGrp firstMap := by
  ext parameter picardClass
  change Pic.map (picardFamilyMap (firstMap ≫ secondMap) parameter.unop) picardClass =
    Pic.map (picardFamilyMap firstMap parameter.unop)
      (Pic.map (picardFamilyMap secondMap parameter.unop) picardClass)
  rw [picardFamilyMap_comp, Pic.map_comp]

/-- The general relative Picard-sheaf pullback morphism. -/
def picardFunctorPullback (morphism : source ⟶ target) :
    picardFunctor target.hom ⟶ picardFunctor source.hom :=
  (presheafToSheaf (fppfTopology.over base) (Type (u + 1))).map
    (picardPresheafPullback morphism)

/-- Pullback preserves the tensor group law on the sheaf. -/
def picardFunctorPullbackGrp (morphism : source ⟶ target) :
    picardFunctorGrp target.hom ⟶ picardFunctorGrp source.hom :=
  sheafifyGrpMap (fppfTopology.over base) (picardPresheafPullbackGrp morphism)

/-- Forgetting the group law recovers the same actual sheaf morphism. -/
theorem picardFunctorPullbackGrp_whiskerRight (morphism : source ⟶ target) :
    CategoryTheory.Functor.whiskerRight (picardFunctorPullbackGrp morphism) (forget GrpCat) =
      (picardFunctorPullback morphism).hom :=
  rfl

/-- The sheaf map is actual pullback on every original line-bundle class. -/
@[simp]
theorem picardFunctorPullback_toPicardFunctor (morphism : source ⟶ target)
    (parameter : Over base) (picardClass : (pullback target.hom parameter.hom).Pic) :
    (picardFunctorPullback morphism).hom.app (.op parameter)
        ((toPicardFunctor target.hom).app (.op parameter) picardClass) =
      (toPicardFunctor source.hom).app (.op parameter)
        (Pic.map (picardFamilyMap morphism parameter) picardClass) :=
  sheafifyGrpMap_toSheafify (fppfTopology.over base)
    (picardPresheafPullbackGrp morphism) (.op parameter) picardClass

@[simp]
theorem picardFunctorPullbackGrp_id :
    picardFunctorPullbackGrp (𝟙 source) = 𝟙 (picardFunctorGrp source.hom) := by
  simp only [picardFunctorPullbackGrp, picardPresheafPullbackGrp_id,
    sheafifyGrpMap_id, picardFunctorGrp]

/-- The sheafified group pullback is contravariantly functorial. -/
theorem picardFunctorPullbackGrp_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdScheme) :
    picardFunctorPullbackGrp (firstMap ≫ secondMap) =
      picardFunctorPullbackGrp secondMap ≫ picardFunctorPullbackGrp firstMap := by
  simp only [picardFunctorPullbackGrp, picardPresheafPullbackGrp_comp, sheafifyGrpMap_comp]

@[simp]
theorem picardFunctorPullback_id :
    picardFunctorPullback (𝟙 source) = 𝟙 (picardFunctor source.hom) := by
  apply Sheaf.hom_ext
  have identity := congrArg
    (fun transformation : picardFunctorGrp source.hom ⟶ picardFunctorGrp source.hom ↦
      CategoryTheory.Functor.whiskerRight transformation (forget GrpCat))
    (picardFunctorPullbackGrp_id (source := source))
  simpa only [picardFunctorPullbackGrp_whiskerRight,
    CategoryTheory.Functor.whiskerRight_id', picardFunctorGrp_comp_forget,
    ObjectProperty.FullSubcategory.id_hom] using identity

/-- The underlying Picard-sheaf pullback is contravariantly functorial. -/
theorem picardFunctorPullback_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdScheme) :
    picardFunctorPullback (firstMap ≫ secondMap) =
      picardFunctorPullback secondMap ≫ picardFunctorPullback firstMap := by
  simp only [picardFunctorPullback, picardPresheafPullback,
    picardPresheafPullbackGrp_comp, CategoryTheory.Functor.whiskerRight_comp,
    CategoryTheory.Functor.map_comp]

/-- Actual bundle pullback characterizes the Picard-sheaf morphism. -/
theorem picardFunctorPullback_unique (morphism : source ⟶ target)
    (candidate : picardFunctor target.hom ⟶ picardFunctor source.hom)
    (compatibility : toPicardFunctor target.hom ≫ candidate.hom =
      picardPresheafPullback morphism ≫ toPicardFunctor source.hom) :
    candidate = picardFunctorPullback morphism := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (fppfTopology.over base) candidate.hom
    (picardFunctorPullback morphism).hom (picardFunctor source.hom).property
  exact compatibility.trans
    (toSheafify_naturality (fppfTopology.over base) (picardPresheafPullback morphism))

end ZInQ.Contrib.CloudR2Poincare.L1
