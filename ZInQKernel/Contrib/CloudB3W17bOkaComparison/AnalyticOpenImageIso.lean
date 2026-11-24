import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.OpenSubspace

/-!
# Actual analytic isomorphism of an open immersion onto its genuine open image

The underlying LRS open-immersion isomorphism is the real range-equality lift.
Its complex linearity follows from its actual factorization through the ambient
analytic morphism. No point-model/topology/analytic-map compatibility is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable {A Z : AnalyticSpace.{0}} (f : A ⟶ Z)
variable [LocallyRingedSpace.IsOpenImmersion f.toLRSHom]

/-- The genuine open image of an actual analytic open immersion. -/
def analyticOpenImage : Opens Z :=
  ⟨Set.range f.toLRSHom.base,
    (PresheafedSpace.IsOpenImmersion.base_open (f := f.toLRSHom.toHom)).isOpen_range⟩

/-- The genuine range equality between the actual immersion and its actual image inclusion. -/
theorem analyticOpenImage_range :
    Set.range f.toLRSHom.base =
      Set.range (Z.toLocallyRingedSpace.ofRestrict (analyticOpenImage f).isOpenEmbedding).base :=
  (LocallyRingedSpace.range_ofRestrict Z.toLocallyRingedSpace (analyticOpenImage f)).symm

/-- The true LRS comparison between the actual open immersion and its actual image restriction. -/
def analyticOpenImageLRSIso :
    A.toLocallyRingedSpace ≅ (Z.restrict (analyticOpenImage f)).toLocallyRingedSpace :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq f.toLRSHom
    (Z.toLocallyRingedSpace.ofRestrict (analyticOpenImage f).isOpenEmbedding)
    (analyticOpenImage_range f)

/-- The real image comparison is over the actual ambient space. -/
theorem analyticOpenImageLRSIso_hom_fac :
    (analyticOpenImageLRSIso f).hom ≫ (Z.ofRestrict (analyticOpenImage f)).toLRSHom = f.toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac f.toLRSHom
    (Z.toLocallyRingedSpace.ofRestrict (analyticOpenImage f).isOpenEmbedding)
    (analyticOpenImage_range f)

/-- The real inverse image comparison is over the same actual ambient space. -/
theorem analyticOpenImageLRSIso_inv_fac :
    (analyticOpenImageLRSIso f).inv ≫ f.toLRSHom = (Z.ofRestrict (analyticOpenImage f)).toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_inv_fac f.toLRSHom
    (Z.toLocallyRingedSpace.ofRestrict (analyticOpenImage f).isOpenEmbedding)
    (analyticOpenImage_range f)

/-- An ACTUAL analytic open immersion identifies its source with its actual open image. -/
def analyticOpenImageIso : A ≅ Z.restrict (analyticOpenImage f) where
  hom := ⟨(analyticOpenImageLRSIso f).hom,
    IsCLinearHom.of_comp (analyticOpenImageLRSIso_hom_fac f) f.isCLinear
      (Z.ofRestrict (analyticOpenImage f)).isCLinear⟩
  inv := ⟨(analyticOpenImageLRSIso f).inv,
    IsCLinearHom.of_comp (analyticOpenImageLRSIso_inv_fac f)
      (Z.ofRestrict (analyticOpenImage f)).isCLinear f.isCLinear⟩
  hom_inv_id := by
    apply AnalyticSpace.forgetToLocallyRingedSpace.map_injective
    exact (analyticOpenImageLRSIso f).hom_inv_id
  inv_hom_id := by
    apply AnalyticSpace.forgetToLocallyRingedSpace.map_injective
    exact (analyticOpenImageLRSIso f).inv_hom_id

/-- The actual analytic source-image isomorphism is over the true original morphism. -/
theorem analyticOpenImageIso_fac :
    (analyticOpenImageIso f).hom ≫ Z.ofRestrict (analyticOpenImage f) = f :=
  AnalyticSpace.forgetToLocallyRingedSpace.map_injective (analyticOpenImageLRSIso_hom_fac f)

/-- Its actual inverse transports the inclusion of the genuine image to the original map. -/
theorem analyticOpenImageIso_inv_fac :
    (analyticOpenImageIso f).inv ≫ f = Z.ofRestrict (analyticOpenImage f) :=
  AnalyticSpace.forgetToLocallyRingedSpace.map_injective (analyticOpenImageLRSIso_inv_fac f)

end ZInQ.Contrib.CloudB3W17bOkaComparison
