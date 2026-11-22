import ZInQKernel.Contrib.CloudR2Poincare.L3.NativeHOneLerayRank
import ZInQKernel.Contrib.CloudR2Poincare.L3.NativeHOneCoefficients
import ZInQKernel.Contrib.CloudR2Poincare.L5.D1FieldNoetherianBaseChange
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The native H¹ dimension bound for a product over a field

The proof uses the actual certified low-degree Leray segment, the sole L5
universe-polymorphic SAME-model proper FIELD base-change algorithm, actual
native H-zero comparisons and actual finite constant-coefficient sheaves.
No Künneth formula, rank/base-change premise, R⁰-vanishing, O-acyclicity,
rational point, CharZero or algebraic-closure assumption is supplied.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L3.HOneProductConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u

/-- Actual native higher direct images of O on the product, as the pullback of
the tilde of the actual cohomology of the second factor. L5 owns the field
base-change algorithm and its certified native suppliers; this only specializes
it to the actual product square and structure coefficient. -/
def productUnitHigherDirectImageIso
    {k : Type u} [Field k] (X Y : Over (Spec (.of k))) [IsProper Y.hom] (j : ℕ) :
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    (Scheme.Modules.higherDirectImage (fst X Y).left j).obj
        (Scheme.Modules.unit (X ⊗ Y).left) ≅
      (Scheme.Modules.pullback X.hom).obj
        ((tilde.functor (.of k)).obj (ModuleCat.of k ((Scheme.Modules.unit Y.left).H j))) := by
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let p := (fst X Y).left
  let a := (snd X Y).left
  let OY := Scheme.Modules.unit Y.left
  haveI : OY.IsFinitePresentation := inferInstance
  have square : IsPullback a p Y.hom X.hom :=
    (IsPullback.of_hasPullback X.hom Y.hom).flip
  exact (Scheme.Modules.higherDirectImage p j).mapIso
      (Scheme.Modules.pullbackObjUnitIso a).symm ≪≫
    L5.FieldBC.nativeProperFieldBaseChangeIso Y.hom OY
      (Scheme.Modules.isFlatOver_of_isInvertible Y.hom OY)
      X.hom a p square j ≪≫
    (Scheme.Modules.pullback X.hom).mapIso
      (L5.FieldBC.nativeFieldHigherDirectImageIsoTildeH Y.hom OY j)

/-- The actual projection pushforward structure sheaf is O_X. This uses the
actual native H⁰(O_Y)≃k, not an assumed rank-one input. -/
def projectionPushforwardUnitIso
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] :
    (Scheme.Modules.pushforward (fst X Y).left).obj
      (Scheme.Modules.unit (X ⊗ Y).left) ≅ Scheme.Modules.unit X.left := by
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  haveI : IsProper (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsProper Y.hom)
  haveI : GeometricallyIntegral (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (GeometricallyIntegral Y.hom)
  let V := ModuleCat.of k ((Scheme.Modules.unit Y.left).H 0)
  let eV : V ≅ ModuleCat.of k k :=
    (HOneCoefficients.unitHZeroLinearEquiv (k := k) (X := Y.left)).symm.toModuleIso
  let eTilde : (tilde.functor (.of k)).obj V ≅ Scheme.Modules.unit (Spec (.of k)) :=
    (tilde.functor (.of k)).mapIso eV ≪≫ tildeSelf
  exact ((Scheme.Modules.pushforward (fst X Y).left).rightDerivedZeroIsoSelf.app
      (Scheme.Modules.unit (X ⊗ Y).left)).symm ≪≫
    productUnitHigherDirectImageIso X Y 0 ≪≫
    (Scheme.Modules.pullback X.hom).mapIso eTilde ≪≫
    Scheme.Modules.pullbackObjUnitIso X.hom

end ZInQ.Contrib.CloudR2Poincare.L3.HOneProductConstruction

namespace ZInQ.Contrib.CloudR2Poincare.L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u

/-- The native H¹ product bound over every field, with all genuine geometric
hypotheses and no supplied dimension/base-change/cohomological premise. -/
theorem nativeHOne_product_dim_le
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
    Module.finrank k ((Scheme.Modules.unit (X ⊗ Y).left).H 1) ≤
      Module.finrank k ((Scheme.Modules.unit X.left).H 1) +
        Module.finrank k ((Scheme.Modules.unit Y.left).H 1) := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
  let p := (fst X Y).left
  let OQ := Scheme.Modules.unit (X ⊗ Y).left
  let OX := Scheme.Modules.unit X.left
  let OY := Scheme.Modules.unit Y.left
  haveI : p.IsOver (Spec (.of k)) := ⟨Over.w (fst X Y)⟩
  haveI : IsProper p := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom))
  have hp : p ≫ X.hom = (X ⊗ Y).hom := Over.w (fst X Y)
  haveI : IsProper ((X ⊗ Y).hom) := by
    rw [← hp]
    infer_instance
  haveI : IsProper ((X ⊗ Y).left ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (X ⊗ Y).hom)
  haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
  haveI : GeometricallyIntegral (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  haveI : IsProper (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsProper Y.hom)
  haveI : Module.Finite k (OQ.H 1) := HOneCoefficients.finite_unit_H 1
  haveI : Module.Finite k (OX.H 1) := HOneCoefficients.finite_unit_H 1
  haveI : Module.Finite k (OY.H 1) := HOneCoefficients.finite_unit_H 1
  let e0 : (Scheme.Modules.pushforward p).obj OQ ≅ OX :=
    HOneProductConstruction.projectionPushforwardUnitIso X Y
  let V1 := ModuleCat.of k (OY.H 1)
  let C1 := (Scheme.Modules.pullback X.hom).obj ((tilde.functor (.of k)).obj V1)
  let e1 : (Scheme.Modules.higherDirectImage p 1).obj OQ ≅ C1 :=
    HOneProductConstruction.productUnitHigherDirectImageIso X Y 1
  haveI : Module.Finite k (((Scheme.Modules.pushforward p).obj OQ).H 1) :=
    Scheme.Modules.finite_H_of_iso (p := X.hom) e0.symm 1 inferInstance
  haveI : Module.Finite k (C1.H 0) := HOneCoefficients.finite_fieldCoefficient_H V1 0
  haveI : Module.Finite k (((Scheme.Modules.higherDirectImage p 1).obj OQ).H 0) :=
    Scheme.Modules.finite_H_of_iso (p := X.hom) e1.symm 0 inferInstance
  have h0 : Module.finrank k (((Scheme.Modules.pushforward p).obj OQ).H 1) =
      Module.finrank k (OX.H 1) := Scheme.Modules.finrankH_congr k e0 1
  have h1 : Module.finrank k (((Scheme.Modules.higherDirectImage p 1).obj OQ).H 0) =
      Module.finrank k (OY.H 1) :=
    (Scheme.Modules.finrankH_congr k e1 0).trans
      (HOneCoefficients.fieldCoefficient_finrankH_zero V1)
  have h := HOneRank.nativeLerayOne_finrank_le (k := k) p OQ
  rw [h0, h1] at h
  exact h

end ZInQ.Contrib.CloudR2Poincare.L3
