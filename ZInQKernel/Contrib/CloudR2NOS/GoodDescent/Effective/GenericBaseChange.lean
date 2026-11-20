/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Actual adapter for lane3's GROUP generic pullback iso to Lane5's generic
OPEN form. The original field/group object and generic base morphism are
retained; only canonical pullback/composition/base-identification maps are
inserted. The V ≅ Spec K identification is explicit until the native DVR
localization adapter supplies it, never a new final NOS hypothesis.
Reuses the compiled lane3 monoidal-natural-transformation lemma, rather
than duplicating its stage/group/properness construction or nominal types.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.CartesianGroup
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.IsoStage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- The native GROUP pullback-composition isomorphism, with the exact
    iterated group image structures and the canonical underlying iso. -/
def pullbackCompGroupIso {S U T : Scheme.{u}} (a : T ⟶ U) (b : U ⟶ S)
    (G : Grp (Over S)) :
    (Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj G) ≅
      (Over.pullback (a ≫ b)).mapGrp.obj G := by
  let G₁ := (Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj G)
  let G₂ := (Over.pullback (a ≫ b)).mapGrp.obj G
  letI : GrpObj ((Over.pullback b ⋙ Over.pullback a).obj G.X) := G₁.grp
  letI : GrpObj ((Over.pullback (a ≫ b)).obj G.X) := G₂.grp
  let E : G₁.X ≅ G₂.X := (Over.pullbackComp a b).symm.app G.X
  haveI : IsMonHom E.hom := ZInQ.Contrib.CloudR2NOS.Spreadout.isMonHom_app_comp
    (F := Over.pullback b) (G := Over.pullback a) (H := Over.pullback (a ≫ b))
    (Over.pullbackComp a b).inv G.X
  exact Grp.mkIso' E

/-- Exact base-morphism congruence as an isomorphism of GROUP objects. -/
def pullbackCongrGroupIso {S T : Scheme.{u}} {a b : T ⟶ S} (h : a = b)
    (G : Grp (Over S)) : (Over.pullback a).mapGrp.obj G ≅ (Over.pullback b).mapGrp.obj G := by
  cases h
  exact Iso.refl _

section Generic
variable {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
    {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))
    (G : Grp (Over U)) (i : V.toScheme ≅ Spec (CommRingCat.of K))
    (j : Spec (CommRingCat.of K) ⟶ S) (hj : i.hom ≫ j = V.ι)

/-- The actual morphism from the stage's generic open to the ORIGINAL-K
    cartesian generic pullback, with no field or scheme replacement. -/
def genericOpenToPullback : (p ⁻¹ᵁ V).toScheme ⟶ pullback p j :=
  pullback.lift (p ⁻¹ᵁ V).ι ((p ∣_ V) ≫ i.hom) (by
    rw [Category.assoc, hj]
    exact (morphismRestrict_ι p V).symm)

@[reassoc (attr := simp)]
theorem genericOpenToPullback_fst :
    genericOpenToPullback p V i j hj ≫ pullback.fst p j = (p ⁻¹ᵁ V).ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem genericOpenToPullback_snd :
    genericOpenToPullback p V i j hj ≫ pullback.snd p j = (p ∣_ V) ≫ i.hom := pullback.lift_snd _ _ _

/-- Preserve the original-K GROUP iso when converting the whole generic
    pullback input to the exact open-subscheme interface of GroupInput.
    No scheme-only iso or unrelated generic group is substituted. -/
def genericGroupIso_open_of_pullback
    (φ : (Over.pullback (pullback.fst p j)).mapGrp.obj G ≅
      (Over.pullback (pullback.snd p j)).mapGrp.obj A) :
    (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback (p ∣_ V)).mapGrp.obj ((Over.pullback i.hom).mapGrp.obj A) := by
  let a := genericOpenToPullback p V i j hj
  exact (pullbackCongrGroupIso (genericOpenToPullback_fst p V i j hj) G).symm ≪≫
    (pullbackCompGroupIso a (pullback.fst p j) G).symm ≪≫
    (Over.pullback a).mapGrp.mapIso φ ≪≫
    pullbackCompGroupIso a (pullback.snd p j) A ≪≫
    pullbackCongrGroupIso (genericOpenToPullback_snd p V i j hj) A ≪≫
    (pullbackCompGroupIso (p ∣_ V) i.hom A).symm

end Generic

#print axioms pullbackCompGroupIso
#print axioms genericOpenToPullback
#print axioms genericGroupIso_open_of_pullback

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
