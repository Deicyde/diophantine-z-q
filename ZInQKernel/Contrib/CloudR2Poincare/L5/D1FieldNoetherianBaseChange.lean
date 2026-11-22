import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeModel
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FlatPullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Field

/-!
# Universe-polymorphic native field-Noetherian SAME-model base change

This thin L5 supplier does NOT import C1, the Type0 AbVar glue, Stacks, or the
arbitrary-base/Noetherian-descent provider. It reuses the already-bound native
Noetherian-field finite-free model. A nonempty model basic open of Spec k is
the whole one-point base. Identity and flat Cartesian base change are compared
through the SAME actual model; exact pullback preserves its homology.

All universes are genuine parameters of the native providers, not transported
from a Type0 proof. This is actual sheaf-isomorphism data, not matching chosen
numerical ranks. The witnesses selected from the native model theorem are
object comparisons; no choice-independent naturality or retained chain/face
homotopy theorem is asserted by this module.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L5.FieldBC

/-- Actual sheaf-level flat base change over a field, through one shared
native finite-free model. No cohomological/base-change premise is supplied. -/
def nativeProperFieldBaseChangeIso
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (N : X.Modules) [N.IsFinitePresentation] (coefficientFlat : N.IsFlatOver f)
    (g : Y ⟶ Spec (.of k)) [Flat g] (a : P ⟶ X) (p : P ⟶ Y)
    (square : IsPullback a p f g) (j : ℕ) :
    (Scheme.Modules.higherDirectImage p j).obj ((Scheme.Modules.pullback a).obj N) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.higherDirectImage f j).obj N) := by
  let S := Spec (.of k)
  have modelExists := Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage_of_isProper
    k f N coefficientFlat (IsLocalRing.closedPoint k)
  let denominator := modelExists.choose
  let U : S.Opens := S.basicOpen denominator
  let Q : CochainComplex U.toScheme.Modules ℤ := modelExists.choose_spec.choose
  have pointIn : IsLocalRing.closedPoint k ∈ U :=
    modelExists.choose_spec.choose_spec.choose_spec.1
  have comparisons : ∀ {T Z : Scheme.{u}} (b : T ⟶ U.toScheme)
      (a' : Z ⟶ X) (p' : Z ⟶ T) [HasInjectiveResolutions Z.Modules],
      IsPullback a' p' f (b ≫ U.ι) → ∀ d : ℕ, Nonempty
        ((((Scheme.Modules.pullback b).mapHomologicalComplex (.up ℤ)).obj Q).homology (d : ℤ) ≅
          (Scheme.Modules.higherDirectImage p' d).obj ((Scheme.Modules.pullback a').obj N)) :=
    modelExists.choose_spec.choose_spec.choose_spec.2.2
  have hU : U = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    simpa only [Subsingleton.elim y (IsLocalRing.closedPoint k)] using pointIn
  haveI : IsIso U.ι := by
    rw [hU]
    exact inferInstanceAs (IsIso S.topIso.hom)
  let topInverse : S ⟶ U.toScheme := inv U.ι
  have topEquation : topInverse ≫ U.ι = 𝟙 S := IsIso.inv_hom_id U.ι
  let C : CochainComplex S.Modules ℤ :=
    ((Scheme.Modules.pullback topInverse).mapHomologicalComplex (.up ℤ)).obj Q
  have originalSquare : IsPullback (𝟙 X) f f (topInverse ≫ U.ι) := by
    rw [topEquation]
    exact IsPullback.id_horiz f
  let originalComparison := (comparisons topInverse (𝟙 X) f originalSquare j).some
  let originalIso : C.homology j ≅ (Scheme.Modules.higherDirectImage f j).obj N :=
    originalComparison ≪≫
      (Scheme.Modules.higherDirectImage f j).mapIso ((Scheme.Modules.pullbackId X).app N)
  have pulledSquare : IsPullback a p f ((g ≫ topInverse) ≫ U.ι) := by
    rw [Category.assoc, topEquation, Category.comp_id]
    exact square
  let pulledComparison := (comparisons (g ≫ topInverse) a p pulledSquare j).some
  let complexComparison :
      ((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((Scheme.Modules.pullback (g ≫ topInverse)).mapHomologicalComplex (.up ℤ)).obj Q :=
    (Functor.mapHomologicalComplexCompIso
      (Scheme.Modules.pullbackComp g topInverse) (.up ℤ)).app Q
  let homologyComparison :
      (((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj C).homology j ≅
        (Scheme.Modules.higherDirectImage p j).obj ((Scheme.Modules.pullback a).obj N) :=
    (HomologicalComplex.homologyFunctor Y.Modules (.up ℤ) (j : ℤ)).mapIso complexComparison ≪≫
      pulledComparison
  exact homologyComparison.symm ≪≫
    (C.sc (j : ℤ)).mapHomologyIso (Scheme.Modules.pullback g) ≪≫
      (Scheme.Modules.pullback g).mapIso originalIso

/-- The ACTUAL original-field native cohomology vector space gives the
higher direct image on Spec k as its associated sheaf, in every universe. -/
def nativeFieldHigherDirectImageIsoTildeH
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [QuasiCompact f] [IsSeparated f] (N : X.Modules) [N.IsQuasicoherent] (j : ℕ) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    (Scheme.Modules.higherDirectImage f j).obj N ≅
      (tilde.functor (.of k)).obj (ModuleCat.of k (N.H j)) := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI : QuasiCompact (X ↘ Spec (.of k)) := by change QuasiCompact f; infer_instance
  haveI : IsSeparated (X ↘ Spec (.of k)) := by change IsSeparated f; infer_instance
  let R := (Scheme.Modules.higherDirectImage f j).obj N
  haveI : IsIso R.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isField (Field.toIsField k) R
  let actualCohomology :=
    (Scheme.Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H N k j).some
  exact (asIso R.fromTildeΓ).symm ≪≫
    (tilde.functor (.of k)).mapIso actualCohomology.toModuleIso

end ZInQ.Contrib.CloudR2Poincare.L5.FieldBC
