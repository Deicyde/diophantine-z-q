import ZInQKernel.Contrib.CloudR2Poincare.L5.C1VanishingCore
import ZInQKernel.Contrib.CloudR2Poincare.L5.D1FieldNoetherianBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FlatPullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Free

/-!
# D1: actual native higher-direct-image base change over a field

The built native universal cohomology model supplies ACTUAL morphism-derived
homology/higher-direct-image comparisons, not matching numerical ranks.
A nonempty model open in Spec k is the whole one-point scheme. Comparing
identity base change and a flat Cartesian base change with this SAME model,
then using exactness of the native flat pullback, proves the sheaf-level
higher-direct-image comparison. Its actual proper/finite-presentation and
relative-coefficient-flatness hypotheses are retained here and discharged
intrinsically for an abelian variety and its invertible coefficient.

The native field-spectrum sections/cohomology comparison then identifies the
original higher direct image with the sheaf associated to ACTUAL N.H j.
No Kunneth formula, Leray premise, chosen-rank model, or supplied BC theorem
is introduced. Native W07 providers/pins are unchanged and already built.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L5

/-- Sheaf-level flat base change for proper finitely presented coefficients
over the field spectrum, derived from a SAME actual universal model. -/
def nativeProperFieldBaseChangeIso
    {k : Type} [Field k] {X Y P : Scheme}
    (f : X ⟶ Spec (.of k)) [IsProper f] [LocallyOfFinitePresentation f]
    (N : X.Modules) [N.IsFinitePresentation] (coefficientFlat : N.IsFlatOver f)
    (g : Y ⟶ Spec (.of k)) [Flat g] (a : P ⟶ X) (p : P ⟶ Y)
    (square : IsPullback a p f g) (j : ℕ) :
    (Scheme.Modules.higherDirectImage p j).obj ((Scheme.Modules.pullback a).obj N) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.higherDirectImage f j).obj N) :=
  FieldBC.nativeProperFieldBaseChangeIso f N coefficientFlat g a p square j

/-- Over Spec k the actual higher direct image is the sheaf associated to
native N.H j, with the exact original-field action, not merely its dimension. -/
def nativeFieldHigherDirectImageIsoTildeH
    {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
    [QuasiCompact f] [IsSeparated f] (N : X.Modules) [N.IsQuasicoherent] (j : ℕ) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    (Scheme.Modules.higherDirectImage f j).obj N ≅
      (tilde.functor (.of k)).obj (ModuleCat.of k (N.H j)) :=
  FieldBC.nativeFieldHigherDirectImageIsoTildeH f N j

/-- The actual sheaf-level product base change needed for the native induction.
Properness, finite presentation and relative coefficient flatness are intrinsic
properties of B and invertible N, not extra cohomological assumptions. -/
def nativeProductHigherDirectImageIso
    {k : Type} [Field k] (B : PkgI3.AbVar k) (N : B.X.left.Modules) [N.IsInvertible] (j : ℕ) :
    letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
    (Scheme.Modules.higherDirectImage (fst B.X B.X).left j).obj
        ((Scheme.Modules.pullback (snd B.X B.X).left).obj N) ≅
      (Scheme.Modules.pullback B.X.hom).obj
        ((tilde.functor (.of k)).obj (ModuleCat.of k (N.H j))) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  haveI : N.IsFinitePresentation := inferInstance
  have square : IsPullback (snd B.X B.X).left (fst B.X B.X).left B.X.hom B.X.hom :=
    (IsPullback.of_hasPullback B.X.hom B.X.hom).flip
  exact nativeProperFieldBaseChangeIso B.X.hom N
    (Scheme.Modules.isFlatOver_of_isInvertible B.X.hom N)
    B.X.hom (snd B.X B.X).left (fst B.X B.X).left square j ≪≫
      (Scheme.Modules.pullback B.X.hom).mapIso
        (nativeFieldHigherDirectImageIsoTildeH B.X.hom N j)

/-- Native cohomology vanishing over the field gives a zero ACTUAL higher
direct image over Spec k. The field-spectrum sections equivalence detects it. -/
theorem nativeFieldHigherDirectImage_isZero_of_subsingleton_H
    {k : Type} [Field k] (B : PkgI3.AbVar k) (N : B.X.left.Modules) [N.IsInvertible]
    (j : ℕ) (vanishes : Subsingleton (N.H j)) :
    IsZero ((Scheme.Modules.higherDirectImage B.X.hom j).obj N) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  letI := vanishes
  haveI : QuasiCompact (B.X.left ↘ Spec (.of k)) := by
    change QuasiCompact B.X.hom
    infer_instance
  haveI : IsSeparated (B.X.left ↘ Spec (.of k)) := by
    change IsSeparated B.X.hom
    infer_instance
  let R := (Scheme.Modules.higherDirectImage B.X.hom j).obj N
  obtain ⟨comparison⟩ :=
    Scheme.Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H N k j
  haveI : Subsingleton ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj R) :=
    comparison.injective.subsingleton
  haveI : Module.Finite k ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj R) := inferInstance
  exact (Scheme.Modules.isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero
    (Field.toIsField k) R).mpr Module.finrank_zero_of_subsingleton

/-- Lower native cohomology vanishing gives actual zero higher direct images
on the product, not a mere equality of chosen ranks. -/
theorem isZero_productHigherDirectImage_of_subsingleton_H
    {k : Type} [Field k] (B : PkgI3.AbVar k) (N : B.X.left.Modules) [N.IsInvertible]
    (j : ℕ) (vanishes : Subsingleton (N.H j)) :
    IsZero ((Scheme.Modules.higherDirectImage (fst B.X B.X).left j).obj
      ((Scheme.Modules.pullback (snd B.X B.X).left).obj N)) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  haveI : N.IsFinitePresentation := inferInstance
  have square : IsPullback (snd B.X B.X).left (fst B.X B.X).left B.X.hom B.X.hom :=
    (IsPullback.of_hasPullback B.X.hom B.X.hom).flip
  let comparison := nativeProperFieldBaseChangeIso B.X.hom N
    (Scheme.Modules.isFlatOver_of_isInvertible B.X.hom N)
    B.X.hom (snd B.X B.X).left (fst B.X B.X).left square j
  exact IsZero.of_iso ((Scheme.Modules.pullback B.X.hom).map_isZero
    (nativeFieldHigherDirectImage_isZero_of_subsingleton_H B N j vanishes)) comparison

end ZInQ.Contrib.CloudR2Poincare.L5
