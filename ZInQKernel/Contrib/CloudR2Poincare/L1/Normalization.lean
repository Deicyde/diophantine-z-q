import ZInQKernel.Contrib.CloudR2Poincare.L1.PolarizationFamily
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RationalPoint

/-!
# Normalized Picard classes and the normalized polarization family

The universal Poincare bundle is normalized at the identity. These definitions
and identities use the actual normalized Picard presheaf, not cohomological
degree zero on a higher-dimensional abelian variety.
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

/-- Normalized classes inject into the Picard SHEAF over every parameter scheme. -/
theorem toPicardFunctor_eq_of_normalized
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (T : Over (Spec (.of k)))
    (M N : (pullback f T.hom).Pic)
    (hM : Pic.map (sectionBaseChange f σ hσ T) M = 1)
    (hN : Pic.map (sectionBaseChange f σ hσ T) N = 1)
    (h : (toPicardFunctor f).app (.op T) M = (toPicardFunctor f).app (.op T) N) :
    M = N := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI : IsProper (X ↘ Spec (.of k)) := by change IsProper f; infer_instance
  haveI : GeometricallyIntegral (X ↘ Spec (.of k)) := by
    change GeometricallyIntegral f
    infer_instance
  let e : (picardFunctorNormalized f σ hσ).toFunctor ≅ (picardFunctor f).obj :=
    normalizedPicardIso (source := X) σ hσ
  let M' : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T) := ⟨M, hM⟩
  let N' : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T) := ⟨N, hN⟩
  have he : e.hom.app (.op T) M' = e.hom.app (.op T) N' := by
    rw [show e.hom = (picardFunctorNormalized f σ hσ).ι ≫ toPicardFunctor f from
      normalizedPicardIso_hom σ hσ]
    exact h
  have hinj : Function.Injective (e.hom.app (.op T)) :=
    Function.LeftInverse.injective (g := e.inv.app (.op T)) (by
      intro z
      exact ConcreteCategory.congr_hom (e.hom_inv_id_app (.op T)) z)
  exact congrArg Subtype.val (hinj he)

/-- The unit section of a group scheme lies over its base. -/
theorem groupUnit_over {S : Scheme.{u}} (A : Over S) [MonObj A] :
    η[A].left ≫ A.hom = 𝟙 S := by
  simpa using Over.w η[A]

/-- The normalized polarization class, removing the parameter's own line-bundle class. -/
def normalizedPolarizationFamily {S : Scheme.{u}} (A : Over S) [MonObj A]
    (L : A.left.Pic) {T : Over S} (x : T ⟶ A) : (pullback A.hom T.hom).Pic :=
  ((picMulEquivProdPicardFunctorNormalized A.hom η[A].left (groupUnit_over A) T
    (polarizationFamily A L x)).2).val

/-- Normalization is genuine triviality along the group unit. -/
theorem normalizedPolarizationFamily_normalized {S : Scheme.{u}} (A : Over S) [MonObj A]
    (L : A.left.Pic) {T : Over S} (x : T ⟶ A) :
    Pic.map (sectionBaseChange A.hom η[A].left (groupUnit_over A) T)
      (normalizedPolarizationFamily A L x) = 1 :=
  ((picMulEquivProdPicardFunctorNormalized A.hom η[A].left (groupUnit_over A) T
    (polarizationFamily A L x)).2).property

/-- Explicit tensor formula for the normalized class (the normalized Mumford family). -/
theorem normalizedPolarizationFamily_formula {S : Scheme.{u}} (A : Over S) [MonObj A]
    (L : A.left.Pic) {T : Over S} (x : T ⟶ A) :
    normalizedPolarizationFamily A L x = polarizationFamily A L x *
      (Pic.map (pullback.snd A.hom T.hom)
        (Pic.map (sectionBaseChange A.hom η[A].left (groupUnit_over A) T)
          (polarizationFamily A L x)))⁻¹ :=
  coe_picMulEquivProdPicardFunctorNormalized_apply_snd A.hom η[A].left (groupUnit_over A)
    T (polarizationFamily A L x)

/-- Over a field-valued parameter no correction remains, because Pic(T)=0. -/
theorem normalizedPolarizationFamily_eq_of_subsingletonPic {S : Scheme.{u}}
    (A : Over S) [MonObj A] (L : A.left.Pic) {T : Over S} [Subsingleton T.left.Pic]
    (x : T ⟶ A) : normalizedPolarizationFamily A L x = polarizationFamily A L x := by
  rw [normalizedPolarizationFamily_formula]
  rw [Subsingleton.elim (Pic.map
    (sectionBaseChange A.hom η[A].left (groupUnit_over A) T)
      (polarizationFamily A L x)) 1, Pic.map_one, inv_one, mul_one]

/-- Pullback from the parameter commutes with change of parameter. -/
theorem pic_map_parameterProjection {S X : Scheme.{u}} (f : X ⟶ S)
    {T T' : Over S} (h : T' ⟶ T) (N : T.left.Pic) :
    Pic.map (JacobianChallenge.baseChangeMap f h) (Pic.map (pullback.snd f T.hom) N) =
      Pic.map (pullback.snd f T'.hom) (Pic.map h.left N) := by
  simp only [← Pic.map_comp, JacobianChallenge.baseChangeMap, pullback.lift_snd]

/-- The normalized family is natural on every parameter scheme. -/
theorem normalizedPolarizationFamily_parameter {S : Scheme.{u}} (A : Over S) [MonObj A]
    (L : A.left.Pic) {T T' : Over S} (x : T ⟶ A) (h : T' ⟶ T) :
    Pic.map (JacobianChallenge.baseChangeMap A.hom h) (normalizedPolarizationFamily A L x) =
      normalizedPolarizationFamily A L (h ≫ x) := by
  rw [normalizedPolarizationFamily_formula, Pic.map_mul, pic_map_inv,
    pic_map_parameterProjection, normalizedPolarizationFamily_formula]
  have hsection : Pic.map (sectionBaseChange A.hom η[A].left (groupUnit_over A) T')
      (polarizationFamily A L (h ≫ x)) =
    Pic.map h.left (Pic.map (sectionBaseChange A.hom η[A].left (groupUnit_over A) T)
      (polarizationFamily A L x)) := by
    rw [← polarizationFamily_parameter L x h, ← Pic.map_comp,
      sectionBaseChange_comp_baseChangeMap, Pic.map_comp]
  rw [polarizationFamily_parameter L x h, hsection]

/-- The zero parameter has the trivial normalized bundle class. -/
@[simp]
theorem normalizedPolarizationFamily_one {S : Scheme.{u}} (A : Over S) [MonObj A]
    (L : A.left.Pic) (T : Over S) : normalizedPolarizationFamily A L (1 : T ⟶ A) = 1 := by
  rw [normalizedPolarizationFamily_formula, polarizationFamily_one, Pic.map_one, Pic.map_one,
    inv_one, mul_one]

end ZInQ.Contrib.CloudR2Poincare.L1
