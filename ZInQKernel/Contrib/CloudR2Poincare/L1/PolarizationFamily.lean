import ZInQKernel.Contrib.CloudR2Poincare.L1.Translation
import ZInQKernel.Contrib.CloudR2Poincare.L1.Functorial
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Monoidal.RepresentableGroup

/-!
# The actual polarization family and Picard classifying morphism

H-72 round 2, L1. We construct the family `t_x^* L ⊗ L⁻¹` using the actual
multiplication morphism of a group scheme and actual pullback on invertible-sheaf
classes. The family is natural on every parameter scheme. When a representing
scheme is supplied, Yoneda turns the family into a scheme morphism and gives
the restriction identity. This is **not** an assertion that the Picard sheaf of
an arbitrary abelian variety is represented: that remaining geometric input is
kept visible in the types.

`Scheme.Pic`, its tensor group law, and its classifying correspondence come from
frenzymath/Jacobian-Challenge at c4254cce15b3e284a0a3ae1d73936f2ee195d272,
Apache-2.0 (see LICENSE/NOTICE and the vendored contribution). The family and
naturality results in this file are new L1 code.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

variable {S : Scheme.{u}}

/-- Pullback commutes with the inverse of an invertible-sheaf class. -/
@[simp]
theorem pic_map_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Pic) :
    Pic.map f L⁻¹ = (Pic.map f L)⁻¹ :=
  (Pic.mapHom f).map_inv L

/-- The value `t_x^* L ⊗ L⁻¹` as an actual Picard class. -/
def translationClass (A : Over S) [MonObj A] (L : A.left.Pic)
    (x : 𝟙_ (Over S) ⟶ A) : A.left.Pic :=
  Pic.map (translate A x).left L * L⁻¹

/-- The pointwise kernel is exactly the translation stabilizer. -/
theorem translationClass_eq_one_iff (A : Over S) [MonObj A] (L : A.left.Pic)
    (x : 𝟙_ (Over S) ⟶ A) :
    translationClass A L x = 1 ↔ Pic.map (translate A x).left L = L := by
  rw [translationClass, mul_inv_eq_one]

/-- Pullback commutes with the polarization class, with no representability assumption. -/
theorem translationClass_pullback {A B : Over S} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] (L : B.left.Pic) (x : 𝟙_ (Over S) ⟶ A) :
    Pic.map f.left (translationClass B L (x ≫ f)) =
      translationClass A (Pic.map f.left L) x := by
  simp only [translationClass, Pic.map_mul, pic_map_inv, ← Pic.map_comp, ← Over.comp_left]
  rw [translate_naturality f x]

/-- The line-bundle class of the translation family on `A × T`. -/
def polarizationFamily (A : Over S) [MonObj A] (L : A.left.Pic)
    {T : Over S} (x : T ⟶ A) : (pullback A.hom T.hom).Pic :=
  Pic.map (translationAction A x).left L * (Pic.map (fst A T).left L)⁻¹

/-- The parameter base-change map is the underlying product morphism. -/
theorem baseChangeMap_eq_tensor {A T T' : Over S} (h : T' ⟶ T) :
    JacobianChallenge.baseChangeMap A.hom h = (𝟙 A ⊗ₘ h).left := by
  apply pullback.hom_ext <;>
    simp [JacobianChallenge.baseChangeMap]

/-- The family map is the underlying product morphism. -/
theorem picardFamilyMap_eq_tensor {A B T : Over S} (f : A ⟶ B) :
    picardFamilyMap f T = (f ⊗ₘ 𝟙 T).left := by
  apply pullback.hom_ext <;> simp [picardFamilyMap]

/-- Actual line-bundle pullback specializes the family over every test scheme. -/
theorem polarizationFamily_parameter {A T T' : Over S} [MonObj A]
    (L : A.left.Pic) (x : T ⟶ A) (h : T' ⟶ T) :
    Pic.map (JacobianChallenge.baseChangeMap A.hom h) (polarizationFamily A L x) =
      polarizationFamily A L (h ≫ x) := by
  rw [baseChangeMap_eq_tensor]
  simp only [polarizationFamily, Pic.map_mul, pic_map_inv, ← Pic.map_comp, ← Over.comp_left]
  rw [translationAction_parameter x h, tensorHom_fst, Category.comp_id]

/-- The family specializes to the translation stabilizer class on rational points. -/
theorem polarizationFamily_rationalPoint (A : Over S) [MonObj A] (L : A.left.Pic)
    (x : 𝟙_ (Over S) ⟶ A) :
    Pic.map (lift (𝟙 A) (toUnit A)).left (polarizationFamily A L x) =
      translationClass A L x := by
  simp only [polarizationFamily, Pic.map_mul, pic_map_inv, ← Pic.map_comp,
    translationClass, ← Over.comp_left]
  rw [translationAction_section A x, lift_fst, Over.id_left, Pic.map_id]

/-- Pulling back the translation family along a homomorphism restricts the line bundle. -/
theorem polarizationFamily_pullback {A B T : Over S} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] (L : B.left.Pic) (x : T ⟶ A) :
    Pic.map (picardFamilyMap f T) (polarizationFamily B L (x ≫ f)) =
      polarizationFamily A (Pic.map f.left L) x := by
  rw [picardFamilyMap_eq_tensor]
  simp only [polarizationFamily, Pic.map_mul, pic_map_inv, ← Pic.map_comp, ← Over.comp_left]
  rw [translationAction_naturality f x, tensorHom_fst]

/-- The zero section has the trivial family class. -/
@[simp]
theorem polarizationFamily_one (A : Over S) [MonObj A] (L : A.left.Pic) (T : Over S) :
    polarizationFamily A L (1 : T ⟶ A) = 1 := by
  simp [polarizationFamily, translationAction]

/-- An actual morphism to a scheme representing the full relative Picard sheaf. -/
def polarizationMorphism (A : Over S) [MonObj A] (L : A.left.Pic)
    {P : Over S} (representation : (picardFunctor A.hom).obj.RepresentableBy P) : A ⟶ P :=
  picardClassifyingHom A.hom representation A (polarizationFamily A L (𝟙 A))

/-- The morphism classifies the requested line bundle on every test scheme. -/
theorem polarizationMorphism_classifies (A : Over S) [MonObj A] (L : A.left.Pic)
    {P T : Over S} (representation : (picardFunctor A.hom).obj.RepresentableBy P)
    (x : T ⟶ A) :
    representation.homEquiv (x ≫ polarizationMorphism A L representation) =
      (toPicardFunctor A.hom).app (.op T) (polarizationFamily A L x) := by
  rw [representation.homEquiv_comp]
  simp only [polarizationMorphism, picardClassifyingHom_apply, Equiv.apply_symm_apply]
  rw [← (toPicardFunctor A.hom).naturality_apply]
  change (toPicardFunctor A.hom).app (.op T)
      (Pic.map (JacobianChallenge.baseChangeMap A.hom x) (polarizationFamily A L (𝟙 A))) = _
  rw [polarizationFamily_parameter, Category.comp_id]

/-- Specialization at the identity is the identity of the represented Picard group. -/
theorem polarizationMorphism_pointed (A : Over S) [MonObj A] (L : A.left.Pic)
    {P : Over S} (representation : (picardFunctor A.hom).obj.RepresentableBy P) :
    letI := picardFunctorCommGrpObj A.hom representation
    η[A] ≫ polarizationMorphism A L representation = η[P] := by
  letI := picardFunctorCommGrpObj A.hom representation
  apply representation.homEquiv.injective
  rw [polarizationMorphism_classifies]
  have unitPoint : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := MonObj.one_eq_one A
  rw [unitPoint, polarizationFamily_one]
  have classifierOne := (picardClassifyingHom A.hom representation (𝟙_ (Over S))).map_one
  apply (representation.homEquiv.symm.injective)
  simpa only [Equiv.symm_apply_apply, picardClassifyingHom_apply,
    MonObj.one_eq_one] using classifierOne

end ZInQ.Contrib.CloudR2Poincare.L1
