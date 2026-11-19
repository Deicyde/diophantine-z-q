/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

The actual TWO chart/projection maps of the tensor-square scheme nerve,
constructed from the frozen group-compatible overlap isomorphism. No
supplied hdesc/effectiveness/unknown properness is assumed. These are the
literal maps consumed by the canonical level-free effective Proj source.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GroupOverlap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorNerve
open TensorCofaces

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R')))
  (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

abbrev model2 : Scheme.{u} := pullback G.X.hom (left R R')
abbrev structure2 : model2 (R := R) R' G ⟶ Square R R' := pullback.snd G.X.hom (left R R')
abbrev projection1 : model2 (R := R) R' G ⟶ G.X.left := pullback.fst G.X.hom (left R R')

/-- The second model projection is the actual constructed GROUP overlap
    isomorphism followed by its literal second-chart projection. -/
def projection2 : model2 (R := R) R' G ⟶ G.X.left :=
  (GroupDatum.overlapSchemeIso (baseMap R R') V G A e c hV
    (left R R') (right R R') (left_base R R')).hom.left ≫ pullback.fst G.X.hom (right R R')

/-- The first square is cartesian by its construction. -/
theorem cartesian1 : IsPullback (projection1 (R := R) R' G) (structure2 (R := R) R' G) G.X.hom (left R R') :=
  IsPullback.of_hasPullback G.X.hom (left R R')

/-- The second square is also cartesian, by the PROVED actual overlap
    isomorphism, not an assumed descent datum. -/
theorem cartesian2 : IsPullback (projection2 R' V G A e c hV) (structure2 (R := R) R' G)
    G.X.hom (right R R') := by
  let E := GroupDatum.overlapSchemeIso (baseMap R R') V G A e c hV
    (left R R') (right R R') (left_base R R')
  let r : model2 (R := R) R' G ⟶ pullback G.X.hom (right R R') := E.hom.left
  have hr : r ≫ pullback.snd G.X.hom (right R R') = structure2 (R := R) R' G := by
    have h := Over.w E.hom
    change r ≫ pullback.snd G.X.hom (right R R') = structure2 (R := R) R' G at h
    exact h
  let E' : model2 (R := R) R' G ≅ pullback G.X.hom (right R R') := (Over.forget _).mapIso E
  refine IsPullback.of_iso_pullback ?_ E' rfl hr
  constructor
  change (r ≫ pullback.fst G.X.hom (right R R')) ≫ G.X.hom =
      structure2 (R := R) R' G ≫ right R R'
  rw [Category.assoc, pullback.condition, ← Category.assoc, hr]

/-- The model2 group is the first-chart pullback of the given model G. -/
abbrev group2 : Grp (Over (Square R R')) := (Over.pullback (left R R')).mapGrp.obj G

/-- Pointwise multiplicativity of projection1 follows from the genuine
    cartesian group-point adjunction, not a supplied structure-law premise. -/
theorem projection1_point_mul {T : Scheme.{u}} (t : T ⟶ Square R R')
    (a b : Over.mk t ⟶ (group2 (R := R) R' G).X) :
    (a * b).left ≫ projection1 (R := R) R' G =
      ((GroupPoints.pullbackPts (left R R') (Over.mk t) G).symm a *
        (GroupPoints.pullbackPts (left R R') (Over.mk t) G).symm b).left := by
  have hm := (GroupPoints.pullbackPts (left R R') (Over.mk t) G).symm.map_mul a b
  exact congrArg Over.Hom.left hm

/-- Pointwise multiplicativity of projection2 is proved using the actual
    IsMonHom of the overlap group morphism plus the pullback point equivalence. -/
theorem projection2_point_mul {T : Scheme.{u}} (t : T ⟶ Square R R')
    (a b : Over.mk t ⟶ (group2 (R := R) R' G).X) :
    (a * b).left ≫ projection2 R' V G A e c hV =
      ((GroupPoints.pullbackPts (right R R') (Over.mk t) G).symm
        (a ≫ (GroupDatum.overlapSchemeIso (baseMap R R') V G A e c hV
          (left R R') (right R R') (left_base R R')).hom) *
       (GroupPoints.pullbackPts (right R R') (Over.mk t) G).symm
        (b ≫ (GroupDatum.overlapSchemeIso (baseMap R R') V G A e c hV
          (left R R') (right R R') (left_base R R')).hom)).left := by
  let E := GroupDatum.overlapSchemeIso (baseMap R R') V G A e c hV
    (left R R') (right R R') (left_base R R')
  haveI : IsMonHom E.hom := GroupDatum.overlapSchemeIso_isMonHom (baseMap R R') V G A e c hV
    (left R R') (right R R') (left_base R R')
  have hm := (GroupPoints.pullbackPts (right R R') (Over.mk t) G).symm.map_mul (a ≫ E.hom) (b ≫ E.hom)
  rw [← MonObj.mul_comp] at hm
  have he := congrArg Over.Hom.left hm
  change ((a * b) ≫ E.hom).left ≫ pullback.fst G.X.hom (right R R') = _ at he
  change (a * b).left ≫ (E.hom.left ≫ pullback.fst G.X.hom (right R R')) =
      ((GroupPoints.pullbackPts (right R R') (Over.mk t) G).symm (a ≫ E.hom) *
        (GroupPoints.pullbackPts (right R R') (Over.mk t) G).symm (b ≫ E.hom)).left
  exact (Category.assoc (a * b).left E.hom.left (pullback.fst G.X.hom (right R R'))).symm.trans he

#print axioms cartesian2
#print axioms projection1_point_mul
#print axioms projection2_point_mul

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorNerve
