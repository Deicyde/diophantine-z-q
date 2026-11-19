/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Transport the actual generic GROUP iso back to the SAME original K and A.
Only the already CONSTRUCTED original generic-open identification and
native categorical composition/identity comparisons are inserted.
No extension field replaces K and no scheme-only iso replaces the GROUP iso.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericBaseChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- The native pullback-identity GROUP comparison, not a scheme-only iso. -/
def pullbackIdGroupIso {S : Scheme.{u}} (A : Grp (Over S)) :
    (Over.pullback (𝟙 S)).mapGrp.obj A ≅ A :=
  (Functor.mapGrpNatIso (Over.pullbackId : Over.pullback (𝟙 S) ≅ 𝟭 (Over S))).app A ≪≫
    Functor.mapGrpIdIso.app A

/-- Original-field generic GROUP iso from the generic-open GROUP iso. -/
def originalFieldGroupIso_of_open
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (V : (Spec (CommRingCat.of R)).Opens) (i : V.toScheme ≅ Spec (CommRingCat.of K))
    (hi : i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) = V.ι)
    (D : Grp (Over (Spec (CommRingCat.of R)))) (A : Grp (Over (Spec (CommRingCat.of K))))
    (E : (Over.pullback V.ι).mapGrp.obj D ≅ (Over.pullback i.hom).mapGrp.obj A) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj D ≅ A := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hbase : i.inv ≫ V.ι = j := by
    calc
      i.inv ≫ V.ι = i.inv ≫ (i.hom ≫ j) := congrArg (i.inv ≫ ·) hi.symm
      _ = j := Iso.inv_hom_id_assoc i j
  exact (pullbackCongrGroupIso hbase D).symm ≪≫
    (pullbackCompGroupIso i.inv V.ι D).symm ≪≫
    (Over.pullback i.inv).mapGrp.mapIso E ≪≫
    pullbackCompGroupIso i.inv i.hom A ≪≫
    pullbackCongrGroupIso i.inv_hom_id A ≪≫ pullbackIdGroupIso A

#print axioms originalFieldGroupIso_of_open

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
