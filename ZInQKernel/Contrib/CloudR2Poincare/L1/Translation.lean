import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Translation identities used in the Picard construction

H-72 round 2, lane L1. These are categorical identities for **actual** morphisms,
not assumptions of the existence of a dual abelian variety. They are stated
before taking line-bundle classes, so the same identities apply over every test
scheme and every extension field.

For comparison, rational translations occur in frenzymath/Jacobian-Challenge
(c4254cce15b3e284a0a3ae1d73936f2ee195d272),
`Jacobian/AlgebraicGeometry/Group/Translations.lean`. The definitions and proofs
below are new, generalized to cartesian monoidal categories, and kept in the
lane namespace to coexist with the vendored source.
-/

noncomputable section

universe v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L1

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Translation by a rational point, as an actual morphism. -/
def translate (A : C) [MonObj A] (x : 𝟙_ C ⟶ A) : A ⟶ A :=
  (toUnit A ≫ x) * 𝟙 A

/-- A monoid homomorphism intertwines translation by a point and its image. -/
theorem translate_naturality {A B : C} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] (x : 𝟙_ C ⟶ A) :
    translate A x ≫ f = f ≫ translate B (x ≫ f) := by
  simp [translate, MonObj.mul_comp, MonObj.comp_mul, Category.assoc]

@[simp]
theorem translate_one (A : C) [MonObj A] : translate A 1 = 𝟙 A := by
  simp [translate]

/-- Translation by a varying `T`-point on `A × T`. -/
def translationAction (A : C) [MonObj A] {T : C} (x : T ⟶ A) : A ⊗ T ⟶ A :=
  (snd A T ≫ x) * fst A T

/-- The translation family specializes to the requested translation. -/
theorem translationAction_section (A : C) [MonObj A] (x : 𝟙_ C ⟶ A) :
    lift (𝟙 A) (toUnit A) ≫ translationAction A x = translate A x := by
  simp [translationAction, translate, MonObj.comp_mul]

/-- Restriction of the parameter scheme commutes with the actual action. -/
theorem translationAction_parameter {A T T' : C} [MonObj A]
    (x : T ⟶ A) (h : T' ⟶ T) :
    (𝟙 A ⊗ₘ h) ≫ translationAction A x = translationAction A (h ≫ x) := by
  simp [translationAction, MonObj.comp_mul]

/-- Restriction along a homomorphism gives the action of its image point. -/
theorem translationAction_naturality {A B T : C} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] (x : T ⟶ A) :
    (f ⊗ₘ 𝟙 T) ≫ translationAction B (x ≫ f) = translationAction A x ≫ f := by
  simp [translationAction, MonObj.comp_mul, MonObj.mul_comp, Category.assoc]

/-- Simultaneous functoriality in the variety and its parameter. -/
theorem translationAction_naturality_parameter {A B T T' : C} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] (x : T ⟶ A) (h : T' ⟶ T) :
    (f ⊗ₘ h) ≫ translationAction B (x ≫ f) =
      translationAction A (h ≫ x) ≫ f := by
  simp [translationAction, MonObj.comp_mul, MonObj.mul_comp, Category.assoc]

end ZInQ.Contrib.CloudR2Poincare.L1
