import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L3.Cartier
import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# The actual finite stabilizer action is a finite-flat equivalence relation

This is the thin native H72 side of the ONE shared Stacks quotient supplier.
R is literally H.K ⊗ A.X; target is the actual action and source the projection.
No quotient-existence or projectivity input is used for this relation geometry.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

variable {k : Type} [Field k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)
    (H : L1.FiniteStabilizerScheme A L)

/-- The action shear (h,a)↦(h,j(h)a), with its actual inverse. -/
def stabilizerActionShear : H.K ⊗ A.X ≅ H.K ⊗ A.X where
  hom := lift (fst H.K A.X) (quotientTarget A L H)
  inv := lift (fst H.K A.X) ((fst H.K A.X ≫ H.j)⁻¹ * snd H.K A.X)
  hom_inv_id := by
    ext <;> simp [quotientTarget, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
      mul_assoc]
  inv_hom_id := by
    ext <;> simp [quotientTarget, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
      mul_assoc]

@[simp] theorem stabilizerActionShear_hom_snd :
    (stabilizerActionShear A L H).hom ≫ snd H.K A.X = quotientTarget A L H := by
  simp [stabilizerActionShear]

/-- Native finite/flat/LFP projection data, the exact finite-locally-free criterion. -/
theorem stabilizer_projection_finite_flat_lfp [CharZero k] :
    IsFinite (snd H.K A.X).left ∧ Flat (snd H.K A.X).left ∧
      LocallyOfFinitePresentation (snd H.K A.X).left := by
  haveI : Smooth H.K.hom := L3.cartierSmooth_proof k H.K inferInstance
  change IsFinite (pullback.snd H.K.hom A.X.hom) ∧
    Flat (pullback.snd H.K.hom A.X.hom) ∧
    LocallyOfFinitePresentation (pullback.snd H.K.hom A.X.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The actual action has the same native finite/flat/LFP properties as the projection. -/
theorem stabilizer_action_finite_flat_lfp [CharZero k] :
    IsFinite (quotientTarget A L H).left ∧ Flat (quotientTarget A L H).left ∧
      LocallyOfFinitePresentation (quotientTarget A L H).left := by
  obtain ⟨hf, ht, hp⟩ := stabilizer_projection_finite_flat_lfp A L H
  haveI := hf
  haveI := ht
  haveI := hp
  have he : (quotientTarget A L H).left =
      (stabilizerActionShear A L H).hom.left ≫ (snd H.K A.X).left := by
    change _ = ((stabilizerActionShear A L H).hom ≫ snd H.K A.X).left
    rw [stabilizerActionShear_hom_snd]
  rw [he]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Reflexivity map for the literal action relation. -/
abbrev stabilizerRelationUnit : A.X ⟶ H.K ⊗ A.X := lift (1 : A.X ⟶ H.K) (𝟙 A.X)

/-- Symmetry map for the literal action relation. -/
abbrev stabilizerRelationInv : H.K ⊗ A.X ⟶ H.K ⊗ A.X :=
  lift (fst H.K A.X)⁻¹ (quotientTarget A L H)

/-- Composition map on the actual source/target pullback of the action relation. -/
abbrev stabilizerRelationComp :
    pullback (snd H.K A.X) (quotientTarget A L H) ⟶ H.K ⊗ A.X :=
  lift ((pullback.fst _ _ ≫ fst H.K A.X) * (pullback.snd _ _ ≫ fst H.K A.X))
    (pullback.snd _ _ ≫ snd H.K A.X)

/-- The actual action/projection pair is an internal equivalence relation. -/
theorem stabilizer_action_isEquivalenceRelation :
    IsEquivalenceRelation (quotientTarget A L H) (snd H.K A.X) := by
  haveI : Mono (quotientRelation A L H) := mono_quotientRelation A L H
  apply EquivalenceRelation.isEquivalenceRelation
  refine {
    right_cancellation := ?_
    r := stabilizerRelationUnit A L H
    reflexivity₁ := ?_
    reflexivity₂ := ?_
    s := stabilizerRelationInv A L H
    symmetry₁ := ?_
    symmetry₂ := ?_
    c := PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition
    isLimit := (IsPullback.of_hasPullback (snd H.K A.X) (quotientTarget A L H)).isLimit
    t := stabilizerRelationComp A L H
    transitivity₁ := ?_
    transitivity₂ := ?_ }
  · intro T f g hf hg
    apply (cancel_mono (quotientRelation A L H)).1
    ext
    · simpa [quotientRelation, Over.comp_left] using congrArg Over.Hom.left hf
    · simpa [quotientRelation, Over.comp_left] using congrArg Over.Hom.left hg
  · simp [stabilizerRelationUnit, quotientTarget, MonObj.comp_mul, MonObj.one_comp]
  · simp [stabilizerRelationUnit]
  · simp [stabilizerRelationInv, quotientTarget, MonObj.comp_mul, GrpObj.inv_comp,
      _root_.mul_assoc]
  · simp [stabilizerRelationInv]
  · change stabilizerRelationComp A L H ≫ quotientTarget A L H =
      pullback.fst (snd H.K A.X) (quotientTarget A L H) ≫ quotientTarget A L H
    have hc := pullback.condition (f := snd H.K A.X) (g := quotientTarget A L H)
    simp only [quotientTarget, MonObj.comp_mul, Category.assoc] at hc
    simp only [stabilizerRelationComp, quotientTarget, MonObj.comp_mul,
      lift_fst_assoc, lift_snd, MonObj.mul_comp, Category.assoc]
    rw [_root_.mul_assoc, ← hc]
  · simp [stabilizerRelationComp]

end ZInQ.Contrib.CloudR2Poincare.L4
