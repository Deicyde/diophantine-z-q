import ZInQKernel.Contrib.CloudR2Poincare.L4.FiniteTypeIntermediate

/-!
# Finite-type descent for the actual finite-flat quotient

Artin–Tate is applied to each affine chart of the target, whose finite preimage
is affine. No finite-type or smoothness property of the quotient is assumed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- Local finite type over k descends through a finite-flat surjection. -/
theorem locallyFiniteType_of_finite_flat_surjective {k : Type} [Field k]
    {A Q : Over (Spec (.of k))} (q : A ⟶ Q) [IsFinite q.left] [Flat q.left]
    [Surjective q.left] [LocallyOfFiniteType A.hom] : LocallyOfFiniteType Q.hom := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) Q.left.affineCover]
  intro i
  let U := Q.left.affineCover.X i
  let ι := Q.left.affineCover.f i
  let V := pullback q.left ι
  let π : V ⟶ U := pullback.snd q.left ι
  let f : U ⟶ Spec (.of k) := ι ≫ Q.hom
  let g : V ⟶ Spec (.of k) := pullback.fst q.left ι ≫ A.hom
  haveI : IsAffine U := inferInstanceAs (IsAffine (Q.left.affineCover.X i))
  haveI : IsFinite π := inferInstanceAs (IsFinite (pullback.snd q.left ι))
  haveI : Flat π := inferInstanceAs (Flat (pullback.snd q.left ι))
  haveI : Surjective π := inferInstanceAs (Surjective (pullback.snd q.left ι))
  haveI : IsAffine V := isAffine_of_isAffineHom π
  haveI : LocallyOfFiniteType g := by dsimp [g]; infer_instance
  have hcomm : π ≫ f = g := by
    dsimp [π, f, g]
    rw [← pullback.condition_assoc, Over.w]
  let R := Γ(U, ⊤)
  let S := Γ(V, ⊤)
  let φ : CommRingCat.of k ⟶ R := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  letI : Algebra k R := φ.hom.toAlgebra
  letI : Algebra R S := π.appTop.hom.toAlgebra
  letI : Algebra k S := (π.appTop.hom.comp φ.hom).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hφ : π.appTop.hom.comp φ.hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom := by
    rw [← hcomm, Scheme.Hom.comp_appTop]
    rfl
  haveI : Algebra.FiniteType k S := by
    change (π.appTop.hom.comp φ.hom).FiniteType
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp
      ((HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := g)).mp inferInstance)
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  haveI : Module.Finite R S := π.finite_appTop
  have hflat : Module.FaithfullyFlat R S :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp ⟨inferInstance, inferInstance⟩
  haveI := hflat
  haveI : Algebra.FiniteType k R := finiteType_of_finite_intermediate k R S
    (FaithfulSMul.algebraMap_injective R S)
  have hφft : φ.hom.FiniteType := inferInstanceAs (Algebra.FiniteType k R)
  have hf : f.appTop = (Scheme.ΓSpecIso (.of k)).hom ≫ φ := by simp [φ]
  apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := f)).mpr
  rw [hf, CommRingCat.hom_comp]
  exact hφft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.surjective)

end ZInQ.Contrib.CloudR2Poincare.L4
