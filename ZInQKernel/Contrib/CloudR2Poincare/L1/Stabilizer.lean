import ZInQKernel.Contrib.CloudR2Poincare.L1.PolarizationFamily

/-!
# The genuine line-bundle stabilizer subgroup functor

H-72 round 2, L1 (quotient route). For an actual group scheme A and an actual
invertible-sheaf class L, this constructs K(L) at the presheaf level. A T-point
x translates A×T over T; it lies in K(L)(T) when that translation preserves L_T.
No Picard-scheme or dual representability is assumed. The functor takes values
in groups on ALL parameter schemes, including nonreduced ones.

The fppf sheafification, its representability by a finite subgroup SCHEME, and
its quotient are additional geometric steps; this file does not silently
replace them with a finite set of geometric points.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L1

section Category

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Translation by a varying point, as an automorphism of the family A×T over T. -/
def familyTranslate (A : C) [MonObj A] {T : C} (x : T ⟶ A) : A ⊗ T ⟶ A ⊗ T :=
  lift (translationAction A x) (snd A T)

@[reassoc (attr := simp)]
theorem familyTranslate_fst (A : C) [MonObj A] {T : C} (x : T ⟶ A) :
    familyTranslate A x ≫ fst A T = translationAction A x :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem familyTranslate_snd (A : C) [MonObj A] {T : C} (x : T ⟶ A) :
    familyTranslate A x ≫ snd A T = snd A T :=
  lift_snd _ _

@[simp]
theorem familyTranslate_one (A : C) [MonObj A] (T : C) :
    familyTranslate A (1 : T ⟶ A) = 𝟙 _ := by
  ext <;> simp [familyTranslate, translationAction]

/-- Composition of translations is translation by the product, in reverse order. -/
theorem familyTranslate_comp (A : C) [MonObj A] {T : C} (x y : T ⟶ A) :
    familyTranslate A x ≫ familyTranslate A y = familyTranslate A (y * x) := by
  ext <;> simp [familyTranslate, translationAction, MonObj.comp_mul, mul_assoc]

/-- The inverse varying point supplies an actual inverse family morphism. -/
def familyTranslateIso (A : C) [GrpObj A] {T : C} (x : T ⟶ A) : A ⊗ T ≅ A ⊗ T where
  hom := familyTranslate A x
  inv := familyTranslate A x⁻¹
  hom_inv_id := by rw [familyTranslate_comp, inv_mul_cancel, familyTranslate_one]
  inv_hom_id := by rw [familyTranslate_comp, mul_inv_cancel, familyTranslate_one]

end Category

open Scheme

variable {S : Scheme.{u}}

/-- The actual pullback of L to the T-family. -/
def parameterLineClass (A : Over S) (L : A.left.Pic) (T : Over S) :
    (A ⊗ T).left.Pic :=
  Pic.map (fst A T).left L

/-- K(L)(T), before fppf sheafification, as a genuine subgroup of A(T). -/
def stabilizerSubgroup (A : Over S) [GrpObj A] (L : A.left.Pic) (T : Over S) :
    Subgroup (T ⟶ A) where
  carrier := {x | Pic.map (familyTranslate A x).left (parameterLineClass A L T) =
    parameterLineClass A L T}
  one_mem' := by simp [familyTranslate_one]
  mul_mem' {x y} hx hy := by
    change Pic.map (familyTranslate A (x * y)).left (parameterLineClass A L T) =
      parameterLineClass A L T
    change Pic.map (familyTranslate A x).left (parameterLineClass A L T) =
      parameterLineClass A L T at hx
    change Pic.map (familyTranslate A y).left (parameterLineClass A L T) =
      parameterLineClass A L T at hy
    rw [← familyTranslate_comp A y x, Over.comp_left, Pic.map_comp, hx, hy]
  inv_mem' {x} hx := by
    have h := congrArg (Pic.map (familyTranslate A x⁻¹).left) hx
    rw [← Pic.map_comp, ← Over.comp_left, familyTranslate_comp, mul_inv_cancel,
      familyTranslate_one, Over.id_left, Pic.map_id] at h
    exact h.symm

/-- The family class is precisely translated L_T tensor L_T inverse. -/
theorem polarizationFamily_eq_translate_parameter (A : Over S) [MonObj A]
    (L : A.left.Pic) {T : Over S} (x : T ⟶ A) :
    polarizationFamily A L x =
      Pic.map (familyTranslate A x).left (parameterLineClass A L T) *
        (parameterLineClass A L T)⁻¹ := by
  simp only [polarizationFamily, parameterLineClass, ← Pic.map_comp, ← Over.comp_left,
    familyTranslate_fst]

/-- Kernel identification before sheafification, valid for every T. -/
theorem polarizationFamily_eq_one_iff_mem_stabilizer (A : Over S) [GrpObj A]
    (L : A.left.Pic) {T : Over S} (x : T ⟶ A) :
    polarizationFamily A L x = 1 ↔ x ∈ stabilizerSubgroup A L T := by
  rw [polarizationFamily_eq_translate_parameter, mul_inv_eq_one]
  rfl

/-- Stabilizing a line bundle is preserved by arbitrary restriction of parameters. -/
theorem stabilizerSubgroup_restriction (A : Over S) [GrpObj A] (L : A.left.Pic)
    {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) (hx : x ∈ stabilizerSubgroup A L T) :
    h ≫ x ∈ stabilizerSubgroup A L T' := by
  rw [← polarizationFamily_eq_one_iff_mem_stabilizer] at hx ⊢
  rw [← polarizationFamily_parameter L x h, hx, Pic.map_one]

/-- The genuine stabilizer as a group-valued presheaf, not an assumed subgroup scheme. -/
def stabilizerPresheafGrp (A : Over S) [GrpObj A] (L : A.left.Pic) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (stabilizerSubgroup A L T.unop)
  map h := GrpCat.ofHom
    { toFun := fun x ↦ ⟨h.unop ≫ x.val, stabilizerSubgroup_restriction A L h.unop x.val x.property⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' x y := Subtype.ext (MonObj.comp_mul _ x.val y.val) }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact Category.id_comp x.val
  map_comp h j := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- The inclusion of K(L)(T) into A(T) is natural and preserves multiplication. -/
def stabilizerPresheafInclusion (A : Over S) [GrpObj A] (L : A.left.Pic) :
    stabilizerPresheafGrp A L ⟶ yonedaGrpObj A where
  app T := GrpCat.ofHom (stabilizerSubgroup A L T.unop).subtype
  naturality _ _ h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    rfl

end ZInQ.Contrib.CloudR2Poincare.L1
