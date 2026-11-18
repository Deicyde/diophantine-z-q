import ZInQKernel.Contrib.CloudR2Poincare.L5.D1FiniteCoefficients
import ZInQKernel.Contrib.CloudR2Poincare.L3.B1EdgeLeray

/-!
# D1: the original universe-zero NativePicZeroVanishing, native-only

Strong induction uses actual lower-zero higher direct images, the actual
native higher-projection and field-base-change coefficient isomorphisms,
L3's proved lower-vanishing edge, and the proved native shear rank comparison.
The edge is used only for zero-group transport, so no field-linearity premise
is supplied. Proper finite cohomology converts the field-rank shear comparison
to actual zero groups. The coefficient H0 groups are the actual N tensor O^r
and O^r groups, not surrogate chosen dimensions.

Every seesaw, H0, finiteness, base-change, projection and Leray ingredient is
proved/imported internally. NO Kunneth formula or extra cohomological premise
occurs in the final theorem. Original interface, objects and pins unchanged.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L5

/-- The exact original universe-zero native Picard-zero vanishing proposition,
with every cohomological and geometric premise discharged. -/
theorem NativePicZeroVanishing_proof : L3.NativePicZeroVanishing.{0} := by
  unfold L3.NativePicZeroVanishing
  intro k _ _ _ B N _ invariant nontrivial q
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  haveI : ∀ j : ℕ, Module.Finite k (N.H j) := native_finiteH_invertible_abVar B N
  have zeroN0 : Subsingleton (N.H 0) :=
    L1.subsingleton_H_zero_of_inversePullback B N nontrivial
      (inverse_pullback_class_of_translationInvariant L1.ReducedGlobalNormalizedSeesaw_proof
        B (Scheme.Pic.mk N) invariant)
  induction q using Nat.strong_induction_on with
  | h q inductionHypothesis =>
    by_cases degreeZero : q = 0
    · subst q
      exact zeroN0
    let P : Scheme := (B.X ⊗ B.X).left
    let base : P ⟶ Spec (.of k) := (B.X ⊗ B.X).hom
    letI : P.Over (Spec (.of k)) := ⟨base⟩
    let p : P ⟶ B.X.left := (fst B.X B.X).left
    let s : P ⟶ B.X.left := (snd B.X B.X).left
    let F2 : P.Modules := (Scheme.Modules.pullback s).obj N
    let F1 : P.Modules := (Scheme.Modules.pullback p).obj N ⊗ F2
    let r : ℕ := N.finrankH k q
    let freeCoefficient : B.X.left.Modules :=
      SheafOfModules.free (R := B.X.left.ringCatSheaf) (Fin r)
    have lowerF2 : ∀ j : ℕ, j < q →
        IsZero ((Scheme.Modules.higherDirectImage p j).obj F2) := by
      intro j lower
      exact isZero_productHigherDirectImage_of_subsingleton_H B N j
        (inductionHypothesis j lower)
    have lowerF1 : ∀ j : ℕ, j < q →
        IsZero ((Scheme.Modules.higherDirectImage p j).obj F1) := by
      intro j lower
      exact isZero_higherDirectImage_tensorPullback_of_isZero p N F2 j (lowerF2 j lower)
    let edgeF1 := L3.native_edge_leray_addEquiv p F1 q lowerF1
    let edgeF2 := L3.native_edge_leray_addEquiv p F2 q lowerF2
    let actualCoefficientF1 : (Scheme.Modules.higherDirectImage p q).obj F1 ≅
        N ⊗ freeCoefficient := nativeTensorProductHigherDirectImageFreeIso B N q
    let actualCoefficientF2 : (Scheme.Modules.higherDirectImage p q).obj F2 ≅
        freeCoefficient := nativeProductHigherDirectImageFreeIso B N q
    haveI : Subsingleton ((N ⊗ freeCoefficient).H 0) :=
      native_subsingleton_H_zero_tensor_free B N r zeroN0
    haveI : Subsingleton (((Scheme.Modules.higherDirectImage p q).obj F1).H 0) :=
      (Scheme.Modules.H.mapLinearEquiv actualCoefficientF1 0).injective.subsingleton
    haveI : Subsingleton (F1.H q) := edgeF1.injective.subsingleton
    have sameNativeRank : F1.finrankH k q = F2.finrankH k q :=
      native_product_tensor_finrankH_eq_secondPullback B N invariant q
    have zeroNativeRankF2 : Module.finrank k (F2.H q) = 0 := by
      change F2.finrankH k q = 0
      rw [← sameNativeRank]
      exact Module.finrank_zero_of_subsingleton
    haveI : IsProper base := by
      haveI : IsProper p := by
        change IsProper (pullback.fst B.X.hom B.X.hom)
        infer_instance
      change IsProper (B.X ⊗ B.X).hom
      rw [← Over.w (fst B.X B.X)]
      change IsProper (p ≫ B.X.hom)
      infer_instance
    haveI : F2.IsFinitePresentation := inferInstance
    haveI : Module.Finite k (F2.H q) := Scheme.Modules.hasFiniteH_of_isProper base F2 q
    haveI : Subsingleton (F2.H q) := Module.finrank_zero_iff.mp zeroNativeRankF2
    haveI : Subsingleton (((Scheme.Modules.higherDirectImage p q).obj F2).H 0) :=
      edgeF2.symm.injective.subsingleton
    haveI : Subsingleton (freeCoefficient.H 0) :=
      (Scheme.Modules.H.mapLinearEquiv actualCoefficientF2.symm 0).injective.subsingleton
    have freeRank : freeCoefficient.finrankH k 0 = r := native_finrankH_free_zero B r
    have actualRankZero : r = 0 := freeRank.symm.trans Module.finrank_zero_of_subsingleton
    change Module.finrank k (N.H q) = 0 at actualRankZero
    exact Module.finrank_zero_iff.mp actualRankZero

end ZInQ.Contrib.CloudR2Poincare.L5
