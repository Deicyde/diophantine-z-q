-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Descent.Morphisms), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Descending morphisms from effective scheme descent data

An effective transport datum identifies precisely the points with equal image in
the descended object. Its invariant morphisms therefore descend uniquely along
the faithfully flat quasi-compact projection.
-/

universe homUniverse categoryUniverse schemeUniverse

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

section General

variable {CategoryType : Type categoryUniverse} [Category.{homUniverse} CategoryType]
  {sourceScheme baseScheme : CategoryType} {baseMap : sourceScheme ⟶ baseScheme} {representation : Over sourceScheme}

lemma transport_eq_of_isPullback (datum : DescentDatum baseMap representation) {descendedObject : Over baseScheme} {descentMap : representation.left ⟶ descendedObject.left}
    (hq : IsPullback descentMap representation.hom descendedObject.hom baseMap)
    (hD : ∀ {testScheme : CategoryType} (f₁ f₂ : testScheme ⟶ sourceScheme) (compatibility : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation),
      (datum.transport f₁ f₂ compatibility point).left ≫ descentMap = point.left ≫ descentMap)
    {testScheme : CategoryType} (f₁ f₂ : testScheme ⟶ sourceScheme) (compatibility : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation) (otherPoint : Over.mk f₂ ⟶ representation)
    (hab : point.left ≫ descentMap = otherPoint.left ≫ descentMap) : datum.transport f₁ f₂ compatibility point = otherPoint := by
  ext
  refine hq.hom_ext ?_ ?_
  · rw [hD, hab]
  · rw [Over.w, Over.w otherPoint]


end General

open AlgebraicGeometry

variable {sourceScheme baseScheme : Scheme.{schemeUniverse}} {baseMap : sourceScheme ⟶ baseScheme} {representation : Over sourceScheme}

lemma existsUnique_desc_of_isPullback [Flat baseMap] [Surjective baseMap] [QuasiCompact baseMap]
    (datum : DescentDatum baseMap representation) {descendedObject : Over baseScheme} {descentMap : representation.left ⟶ descendedObject.left}
    (hq : IsPullback descentMap representation.hom descendedObject.hom baseMap)
    (hD : ∀ {testScheme : Scheme.{schemeUniverse}} (f₁ f₂ : testScheme ⟶ sourceScheme) (compatibility : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation),
      (datum.transport f₁ f₂ compatibility point).left ≫ descentMap = point.left ≫ descentMap)
    {targetScheme : Scheme.{schemeUniverse}} (invariantMap : representation.left ⟶ targetScheme)
    (hg : ∀ {testScheme : Scheme.{schemeUniverse}} (f₁ f₂ : testScheme ⟶ sourceScheme) (compatibility : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation),
      (datum.transport f₁ f₂ compatibility point).left ≫ invariantMap = point.left ≫ invariantMap) :
    ∃! descendedMap : descendedObject.left ⟶ targetScheme, descentMap ≫ descendedMap = invariantMap := by
  have : Flat descentMap := MorphismProperty.of_isPullback hq.flip inferInstance
  have : Surjective descentMap := MorphismProperty.of_isPullback hq.flip inferInstance
  have : QuasiCompact descentMap := MorphismProperty.of_isPullback hq.flip inferInstance
  have hw (testScheme : Scheme.{schemeUniverse}) (g₁ g₂ : testScheme ⟶ representation.left) (h₁₂ : g₁ ≫ descentMap = g₂ ≫ descentMap) : g₁ ≫ invariantMap = g₂ ≫ invariantMap := by
    have hp : (g₁ ≫ representation.hom) ≫ baseMap = (g₂ ≫ representation.hom) ≫ baseMap := by
      rw [Category.assoc, Category.assoc, ← hq.w, reassoc_of% h₁₂]
    have := datum.transport_eq_of_isPullback hq hD _ _ hp
      (Over.homMk (U := Over.mk (g₁ ≫ representation.hom)) g₁ rfl)
      (Over.homMk (U := Over.mk (g₂ ≫ representation.hom)) g₂ rfl) h₁₂
    have h' := hg _ _ hp (Over.homMk (U := Over.mk (g₁ ≫ representation.hom)) g₁ rfl)
    rw [this] at h'
    exact h'.symm
  refine ⟨EffectiveEpi.desc descentMap invariantMap (fun g₁ g₂ compatibility ↦ hw _ g₁ g₂ compatibility), EffectiveEpi.fac _ _ _,
    fun descendedMap hg₀ ↦ ?_⟩
  rw [← cancel_epi descentMap, hg₀, EffectiveEpi.fac]


end CategoryTheory.Over.DescentDatum
