import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.PullbackSupport

/-!
Vanishing loci of actual module inclusions are invariant under an isomorphism
of their source. This is the elementary consumer needed after the real GAGA lift
supplies its specific inclusion equation; it is not a replacement GAGA premise.
-/

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

/-- Precomposing an actual inclusion with a module isomorphism does not change its
non-surjectivity locus on actual canonical stalks. -/
theorem vanishingLocus_iso_source {X : LocallyRingedSpace.{u}}
    {M N : SheafOfModules.{u} X.ringSheaf} (e : M ≅ N)
    (j : N ⟶ SheafOfModules.unit X.ringSheaf) :
    ZInQ.Contrib.CloudB3W17bAnalyticIdeal.vanishingLocus (e.hom ≫ j) =
      ZInQ.Contrib.CloudB3W17bAnalyticIdeal.vanishingLocus j := by
  ext x
  change ¬ Function.Surjective ((X.stalkFunctor x).map (e.hom ≫ j)) ↔
    ¬ Function.Surjective ((X.stalkFunctor x).map j)
  have he : Function.Surjective ((X.stalkFunctor x).map e.hom) :=
    (ConcreteCategory.bijective_of_isIso _).2
  have hmap : ⇑((X.stalkFunctor x).map (e.hom ≫ j)) =
      ⇑((X.stalkFunctor x).map j) ∘ ⇑((X.stalkFunctor x).map e.hom) := by
    funext t
    rw [Functor.map_comp]
    rfl
  rw [hmap]
  exact not_congr (Function.Surjective.of_comp_iff _ he)

end ZInQ.Contrib.CloudB3W17bCanonicalImage
