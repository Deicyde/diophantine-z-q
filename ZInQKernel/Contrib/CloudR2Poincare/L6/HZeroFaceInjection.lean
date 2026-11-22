import ZInQKernel.Contrib.CloudR2Poincare.L6.ProductGeometry
/-!
# Actual native H⁰ product-face injection and initial unit ranks

The first face is split-surjective in H⁰ by actual pullback comp/id. Its
source and target both have rank one by actual proper geometric integrality,
so its kernel vanishes. The pair is therefore injective. This does not use
H¹(O)=0, an assumed Cech/H comparison, or any supplied rank/model premise.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- Actual degree-zero face pullback is split-surjective by the literal projection pullback. -/
theorem nativeHZero_faceX_surjective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    Function.Surjective (nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 0) := by
  have hcomp : (lift (𝟙 X) (toUnit X ≫ y)).left ≫ (fst X Y).left = 𝟙 X.left := by
    change (lift (𝟙 X) (toUnit X ≫ y) ≫ fst X Y).left = (𝟙 X : X ⟶ X).left
    rw [lift_fst]
  have hr : Function.RightInverse (nativeUnitHPullback (fst X Y).left 0)
      (nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 0) := by
    intro a
    change ((nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 0).comp
      (nativeUnitHPullback (fst X Y).left 0)) a = a
    rw [← nativeUnitHPullback_comp, hcomp, nativeUnitHPullback_id]
    rfl
  exact hr.surjective

/-- Actual first-face H⁰ injection from proper/geometrically-integral unit ranks. -/
theorem nativeHZero_faceX_injective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    Function.Injective (nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 0) := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
  haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
  haveI : GeometricallyIntegral (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  haveI : IsProper (fst X Y).left := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom))
  haveI : GeometricallyIntegral (fst X Y).left :=
    inferInstanceAs (GeometricallyIntegral (pullback.fst X.hom Y.hom))
  haveI : IsProper (X ⊗ Y).hom := by rw [← Over.w (fst X Y)]; infer_instance
  haveI : GeometricallyIntegral (X ⊗ Y).hom := nativeProduct_geometricallyIntegral X Y
  haveI : IsProper ((X ⊗ Y).left ↘ Spec (.of k)) := inferInstanceAs (IsProper (X ⊗ Y).hom)
  haveI : GeometricallyIntegral ((X ⊗ Y).left ↘ Spec (.of k)) :=
    inferInstanceAs (GeometricallyIntegral (X ⊗ Y).hom)
  haveI : Module.Finite k ((Scheme.Modules.unit X.left).H 0) :=
    ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.finite_unit_H 0
  haveI : Module.Finite k ((Scheme.Modules.unit (X ⊗ Y).left).H 0) :=
    ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.finite_unit_H 0
  let F := nativeUnitHPullbackLinearMap X (X ⊗ Y) (lift (𝟙 X) (toUnit X ≫ y)) 0
  have hsur : Function.Surjective F := nativeHZero_faceX_surjective X Y y
  have hdim : Module.finrank k ((Scheme.Modules.unit (X ⊗ Y).left).H 0) ≤
      Module.finrank k ((Scheme.Modules.unit X.left).H 0) := by
    rw [ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.unit_finrankH_zero,
      ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.unit_finrankH_zero]
  have hR : Module.finrank k (LinearMap.range F) =
      Module.finrank k ((Scheme.Modules.unit X.left).H 0) := by
    rw [LinearMap.range_eq_top.mpr hsur]
    exact Submodule.topEquiv.finrank_eq
  have hr : Module.finrank k (LinearMap.range F) + Module.finrank k (LinearMap.ker F) =
      Module.finrank k ((Scheme.Modules.unit (X ⊗ Y).left).H 0) := by
    have h := (LinearMap.ker F).finrank_quotient_add_finrank
    rwa [F.quotKerEquivRange.finrank_eq] at h
  have hk : Module.finrank k (LinearMap.ker F) = 0 := by rw [hR] at hr; omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The literal native degree-zero two-face pair is injective; no Cech/model premise. -/
theorem nativeHZero_twoFaces_injective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    Function.Injective (fun z : (Scheme.Modules.unit (X ⊗ Y).left).H 0 =>
      (nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 0 z,
        nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 0 z)) := by
  intro a b hab
  apply nativeHZero_faceX_injective X Y y
  exact congrArg Prod.fst hab

end ZInQ.Contrib.CloudR2Poincare.L6
