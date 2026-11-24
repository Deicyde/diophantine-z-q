/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

The generic GROUP identification survives the ACTUAL base refinement.
This is a consumer of the already compiled native group pullback-composition
bridge, not a replacement generic scheme iso or finite-stage model supplier.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericBaseChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Base-change the given GROUP iso over the whole original generic
    fibre, retaining the actual refinement morphism and original group A. -/
def genericPullbackGroupIso_baseChange
    {S U U' T : Scheme.{u}} (p : U ⟶ S) (p' : U' ⟶ S)
    (a : U' ⟶ U) (ha : a ≫ p = p') (j : T ⟶ S)
    (G : Grp (Over U)) (A : Grp (Over T))
    (φ : (Over.pullback (pullback.fst p j)).mapGrp.obj G ≅
      (Over.pullback (pullback.snd p j)).mapGrp.obj A) :
    (Over.pullback (pullback.fst p' j)).mapGrp.obj ((Over.pullback a).mapGrp.obj G) ≅
      (Over.pullback (pullback.snd p' j)).mapGrp.obj A := by
  let t : pullback p' j ⟶ pullback p j :=
    pullback.lift (pullback.fst p' j ≫ a) (pullback.snd p' j)
      (by rw [Category.assoc, ha]; exact pullback.condition)
  have ht₁ : t ≫ pullback.fst p j = pullback.fst p' j ≫ a := pullback.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd p j = pullback.snd p' j := pullback.lift_snd _ _ _
  exact pullbackCompGroupIso (pullback.fst p' j) a G ≪≫
    (pullbackCongrGroupIso ht₁ G).symm ≪≫
    (pullbackCompGroupIso t (pullback.fst p j) G).symm ≪≫
    (Over.pullback t).mapGrp.mapIso φ ≪≫
    pullbackCompGroupIso t (pullback.snd p j) A ≪≫
    pullbackCongrGroupIso ht₂ A

#print axioms genericPullbackGroupIso_baseChange

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
