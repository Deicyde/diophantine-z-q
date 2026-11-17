/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Nominal bridge from the SAME native group objects/points to the canonical
H76 relative group laws. No new nominal group/law definition is introduced.
The real source law and group constructor are reused, preserving credits.
-/
import ZInQKernel.Contrib.CloudR2NOS.AVInput
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorSquare
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Native point transport through an actual morphism over a base map. -/
def pointMapOver
    {R S : Type u} [CommRing R] [CommRing S]
    (G : Grp (Over (Spec (CommRingCat.of R)))) (H : Grp (Over (Spec (CommRingCat.of S))))
    (p : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (q : H.X.left ⟶ G.X.left)
    (hq : q ≫ G.X.hom = H.X.hom ≫ p) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (x : Over.mk t ⟶ H.X) : Over.mk (t ≫ p) ⟶ G.X :=
  Over.homMk (x.left ≫ q) (by
    change (x.left ≫ q) ≫ G.X.hom = t ≫ p
    rw [Category.assoc, hq, ← Category.assoc]
    have hx : x.left ≫ H.X.hom = t := by simpa only [Over.mk_hom] using Over.w x
    rw [hx])

/-- The source's multiplication-compatibility statement follows from
    actual multiplication on native points, retaining all base morphisms. -/
theorem law_comp_of_native_points
    {R S : Type u} [CommRing R] [CommRing S]
    (G : Grp (Over (Spec (CommRingCat.of R)))) (H : Grp (Over (Spec (CommRingCat.of S))))
    (p : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (q : H.X.left ⟶ G.X.left)
    (hq : q ≫ G.X.hom = H.X.hom ≫ p)
    (hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : Over.mk t ⟶ H.X),
      (x * y).left ≫ q = (pointMapOver G H p q hq t x * pointMapOver G H p q hq t y).left) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t H.X.hom),
      ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp H).mul t x y).1 ≫ q =
      ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp G).mul (t ≫ p)
        ⟨x.1 ≫ q, by rw [Category.assoc, hq, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ q, by rw [Category.assoc, hq, ← Category.assoc, y.2]⟩).1 := by
  intro T t x y
  let x' : Over.mk t ⟶ H.X := schemeHomOverToOverHom x
  let y' : Over.mk t ⟶ H.X := schemeHomOverToOverHom y
  change (x' * y').left ≫ q =
    (pointMapOver G H p q hq t x' * pointMapOver G H p q hq t y').left
  exact hm t x' y'

namespace TensorNerve
open TensorCofaces

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

/-- Genuine first-projection source-law compatibility, with no supplied
    relative group law or compatibility premise. -/
theorem source_projection1_mul :
    ∀ {T : Scheme.{u}} (t : T ⟶ Square R R')
      (x y : SchemeHomOver t (structure2 (R := R) R' G)),
      ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp (group2 (R := R) R' G)).mul t x y).1 ≫ projection1 (R := R) R' G =
      ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp G).mul (t ≫ left R R')
        ⟨x.1 ≫ projection1 (R := R) R' G, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ projection1 (R := R) R' G, by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩).1 := by
  apply law_comp_of_native_points G (group2 (R := R) R' G) (left R R') (projection1 (R := R) R' G) (pullback.condition)
  intro T t x y
  let F := GroupPoints.pullbackPts (left R R') (Over.mk t) G
  have hx : pointMapOver G (group2 (R := R) R' G) (left R R') (projection1 (R := R) R' G) (pullback.condition) t x = F.symm x := by
    apply Over.OverMorphism.ext
    rfl
  have hy : pointMapOver G (group2 (R := R) R' G) (left R R') (projection1 (R := R) R' G) (pullback.condition) t y = F.symm y := by
    apply Over.OverMorphism.ext
    rfl
  rw [hx, hy]
  exact projection1_point_mul (R := R) R' G t x y

/-- Genuine second-projection compatibility, using the PROVED group
    overlap isomorphism rather than an assumed IsMonHom/relative law. -/
theorem source_projection2_mul :
    ∀ {T : Scheme.{u}} (t : T ⟶ Square R R')
      (x y : SchemeHomOver t (structure2 (R := R) R' G)),
      ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp (group2 (R := R) R' G)).mul t x y).1 ≫ projection2 R' V G A e c hV =
      ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp G).mul (t ≫ right R R')
        ⟨x.1 ≫ projection2 R' V G A e c hV, by rw [Category.assoc, (cartesian2 R' V G A e c hV).w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ projection2 R' V G A e c hV, by rw [Category.assoc, (cartesian2 R' V G A e c hV).w, ← Category.assoc, y.2]⟩).1 := by
  apply law_comp_of_native_points G (group2 (R := R) R' G) (right R R')
    (projection2 R' V G A e c hV) (cartesian2 R' V G A e c hV).w
  intro T t x y
  let E := GroupDatum.overlapSchemeIso (baseMap R R') V G A e c hV (left R R') (right R R') (left_base R R')
  let F := GroupPoints.pullbackPts (right R R') (Over.mk t) G
  have hx : pointMapOver G (group2 (R := R) R' G) (right R R') (projection2 R' V G A e c hV)
      (cartesian2 R' V G A e c hV).w t x = F.symm (x ≫ E.hom) := by
    apply Over.OverMorphism.ext
    change x.left ≫ (E.hom.left ≫ pullback.fst G.X.hom (right R R')) =
      (x.left ≫ E.hom.left) ≫ pullback.fst G.X.hom (right R R')
    exact (Category.assoc ..).symm
  have hy : pointMapOver G (group2 (R := R) R' G) (right R R') (projection2 R' V G A e c hV)
      (cartesian2 R' V G A e c hV).w t y = F.symm (y ≫ E.hom) := by
    apply Over.OverMorphism.ext
    change y.left ≫ (E.hom.left ≫ pullback.fst G.X.hom (right R R')) =
      (y.left ≫ E.hom.left) ≫ pullback.fst G.X.hom (right R R')
    exact (Category.assoc ..).symm
  rw [hx, hy]
  exact projection2_point_mul R' V G A e c hV t x y

end TensorNerve

#print axioms law_comp_of_native_points
#print axioms TensorNerve.source_projection1_mul
#print axioms TensorNerve.source_projection2_mul

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
