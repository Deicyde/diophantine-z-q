import ZInQKernel.Contrib.CloudB3W17bOkaComparison.PointClosedDictionary
import Mathlib.Algebra.Field.ULift

/-!
# Actual complex schemes over Oka's lifted complex base

Oka's universe-polymorphic scheme category uses `Spec (ULift ℂ)`.  The adapter
below changes only the structure morphism along the genuine base isomorphism;
the underlying scheme is unchanged.  Rational points are carried by actual
scheme morphisms, with the same underlying closed point.  This does not assume
that a set map is an analytic morphism.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- The genuine base isomorphism used by Oka's universe-zero scheme objects. -/
def complexULiftBaseIso :
    Spec (CommRingCat.of ℂ) ≅ Spec (CommRingCat.of (ULift.{0} ℂ)) where
  hom := Spec.map (ULift.ringEquiv (R := ℂ)).toCommRingCatIso.hom
  inv := Spec.map (ULift.ringEquiv (R := ℂ)).toCommRingCatIso.inv
  hom_inv_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  inv_hom_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]

/-- The same scheme, with structure map expressed over Oka's actual lifted base. -/
def overULift (X : Over (Spec (CommRingCat.of ℂ))) :
    Over (Spec (CommRingCat.of (ULift.{0} ℂ))) :=
  Over.mk (X.hom ≫ complexULiftBaseIso.hom)

@[simp]
theorem overULift_left (X : Over (Spec (CommRingCat.of ℂ))) : (overULift X).left = X.left := rfl

instance overULift_locallyOfFiniteType (X : Over (Spec (CommRingCat.of ℂ)))
    [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (overULift X).hom := by
  dsimp [overULift]
  infer_instance

instance overULift_smooth (X : Over (Spec (CommRingCat.of ℂ)))
    [Smooth X.hom] : Smooth (overULift X).hom := by
  dsimp [overULift]
  infer_instance

instance overULift_proper (X : Over (Spec (CommRingCat.of ℂ)))
    [IsProper X.hom] : IsProper (overULift X).hom := by
  dsimp [overULift]
  infer_instance

/-- An actual scheme morphism, with only its base spelling changed. -/
def overULiftMap {X Y : Over (Spec (CommRingCat.of ℂ))} (f : X ⟶ Y) :
    overULift X ⟶ overULift Y :=
  Over.homMk f.left (by
    change f.left ≫ (Y.hom ≫ complexULiftBaseIso.hom) = X.hom ≫ complexULiftBaseIso.hom
    rw [← Category.assoc, Over.w f])

/-- The actual native point over the lifted base; the equivalence is precomposition by a base iso. -/
def pointULiftEquiv (X : Over (Spec (CommRingCat.of ℂ))) :
    ComplexPoint X ≃ Point (ULift.{0} ℂ) (overULift X) where
  toFun p := Over.homMk (complexULiftBaseIso.inv ≫ p.left) (by
    have hp : p.left ≫ X.hom = 𝟙 _ := by simpa using Over.w p
    change (complexULiftBaseIso.inv ≫ p.left) ≫
      (X.hom ≫ complexULiftBaseIso.hom) = 𝟙 _ ≫ 𝟙 _
    calc
      (complexULiftBaseIso.inv ≫ p.left) ≫ (X.hom ≫ complexULiftBaseIso.hom) =
          complexULiftBaseIso.inv ≫ (p.left ≫ X.hom) ≫ complexULiftBaseIso.hom := by
            simp only [Category.assoc]
      _ = 𝟙 _ ≫ 𝟙 _ := by rw [hp]; simp)
  invFun p := Over.homMk (complexULiftBaseIso.hom ≫ p.left) (by
    let q : Spec (CommRingCat.of (ULift.{0} ℂ)) ⟶ X.left := p.left
    have hp : q ≫ (X.hom ≫ complexULiftBaseIso.hom) = 𝟙 _ := by
      simpa [q, overULift] using Over.w p
    change (complexULiftBaseIso.hom ≫ q) ≫ X.hom = 𝟙 _ ≫ 𝟙 _
    apply (cancel_mono complexULiftBaseIso.hom).mp
    calc
      ((complexULiftBaseIso.hom ≫ q) ≫ X.hom) ≫ complexULiftBaseIso.hom =
          complexULiftBaseIso.hom ≫ (q ≫ (X.hom ≫ complexULiftBaseIso.hom)) :=
        (Category.assoc _ _ _).trans (Category.assoc _ _ _)
      _ = complexULiftBaseIso.hom ≫ 𝟙 _ := congrArg (fun m => complexULiftBaseIso.hom ≫ m) hp
      _ = (𝟙 _ ≫ 𝟙 _) ≫ complexULiftBaseIso.hom := by
        simp only [Category.id_comp, Category.comp_id])
  left_inv p := by
    apply Over.OverMorphism.ext
    let q : Spec (CommRingCat.of ℂ) ⟶ X.left := p.left
    change complexULiftBaseIso.hom ≫ (complexULiftBaseIso.inv ≫ q) = q
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ q) complexULiftBaseIso.hom_inv_id).trans (Category.id_comp _))
  right_inv p := by
    apply Over.OverMorphism.ext
    let q : Spec (CommRingCat.of (ULift.{0} ℂ)) ⟶ X.left := p.left
    change complexULiftBaseIso.inv ≫ (complexULiftBaseIso.hom ≫ q) = q
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ q) complexULiftBaseIso.inv_hom_id).trans (Category.id_comp _))

/-- Lifted-base native points have exactly the original underlying scheme point. -/
theorem pointULiftEquiv_underlying (X : Over (Spec (CommRingCat.of ℂ))) (p : ComplexPoint X) :
    (pointULiftEquiv X p).underlying = p.underlying := by
  change p.left (complexULiftBaseIso.inv (IsLocalRing.closedPoint (ULift.{0} ℂ))) =
    p.left (IsLocalRing.closedPoint ℂ)
  congr 1
  exact Subsingleton.elim (α := Spec (CommRingCat.of ℂ)) _ _

/-- The lifted-base point dictionary respects actual scheme maps. -/
theorem pointULiftEquiv_map {X Y : Over (Spec (CommRingCat.of ℂ))} (f : X ⟶ Y)
    (p : ComplexPoint X) :
    pointULiftEquiv Y (Point.map f p) = Point.map (overULiftMap f) (pointULiftEquiv X p) := by
  apply Over.OverMorphism.ext
  change complexULiftBaseIso.inv ≫ (p.left ≫ f.left) =
    (complexULiftBaseIso.inv ≫ p.left) ≫ f.left
  exact (Category.assoc _ _ _).symm

/-- ORIGINAL CPts, as genuine points over Oka's actual base. -/
def originalPointULiftEquiv (X : Over (Spec (CommRingCat.of ℂ))) :
    CloudB3W17Hodge.CPt X ≃ Point (ULift.{0} ℂ) (overULift X) :=
  (CloudB3W17Hodge.cptEquiv X).trans (pointULiftEquiv X)

end ZInQ.Contrib.CloudB3W17bOkaComparison
