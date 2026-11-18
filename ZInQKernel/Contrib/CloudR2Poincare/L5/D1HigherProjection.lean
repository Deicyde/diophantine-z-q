import ZInQKernel.Contrib.CloudR2Poincare.L5.B1EvaluationBridge
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# D1: native higher projection formula for an invertible coefficient

The underived native projection formula is an actual natural isomorphism.
Tensoring by an invertible module is an exact equivalence and preserves
injectives. Mapping a chosen injective resolution by this equivalence gives
an actual injective resolution. The three proved comparisons (exact
postcomposition, the underived natural isomorphism, and equivalence
precomposition) therefore give the higher projection formula in every degree.

No higher projection-formula, Leray, Kunneth, acyclicity, or rank premise is
supplied. This module adds only L5-local data/proofs and imports the unchanged
already-built native W07 provider.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L5

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- The literal comparison between a single object in degree zero and its
image under an additive functor. Positive terms are actual zero objects. -/
def mappedSingleZeroIso (E : C ⥤ D) [E.Additive] (M : C) :
    (CochainComplex.single₀ D).obj (E.obj M) ≅
      (E.mapHomologicalComplex (.up ℕ)).obj ((CochainComplex.single₀ C).obj M) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => by
    cases n with
    | zero => exact Iso.refl _
    | succ n =>
      have hsource : IsZero (((CochainComplex.single₀ D).obj (E.obj M)).X (n + 1)) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
      have htarget : IsZero (E.obj (((CochainComplex.single₀ C).obj M).X (n + 1))) :=
        E.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
      exact { hom := 0, inv := 0
              hom_inv_id := hsource.eq_of_src _ _
              inv_hom_id := htarget.eq_of_src _ _ })
    (by intro i j _; simp)

/-- Transporting an actual injective resolution through an exact equivalence.
Its augmentation is the mapped original augmentation, not a numerical model. -/
def injectiveResolutionMapEquivalence (E : C ≌ D) [E.functor.Additive]
    {M : C} (I : InjectiveResolution M) : InjectiveResolution (E.functor.obj M) where
  cocomplex := (E.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective n := (E.map_injective_iff (I.cocomplex.X n)).mpr (by infer_instance)
  ι := (mappedSingleZeroIso E.functor M).hom ≫
    (E.functor.mapHomologicalComplex (.up ℕ)).map I.ι
  quasiIso := by infer_instance

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  {A : Type*} [Category* A] [Abelian A]

/-- Precomposition by an exact equivalence commutes with right derivation,
computed by mapping the SAME native injective resolution. -/
def rightDerivedPrecomposeEquivalenceIso (E : C ≌ D) [E.functor.Additive]
    (F : D ⥤ A) [F.Additive] (M : C) (q : ℕ) :
    ((E.functor ⋙ F).rightDerived q).obj M ≅
      (F.rightDerived q).obj (E.functor.obj M) := by
  let I := injectiveResolution M
  let J := injectiveResolutionMapEquivalence E I
  exact I.isoRightDerivedObj (E.functor ⋙ F) q ≪≫
    (J.isoRightDerivedObj F q).symm

end General

universe u

/-- The actual higher projection formula for every scheme morphism and
invertible target coefficient, with no added geometric or cohomological
hypothesis. Canonical resolution and native tensor maps give this data. -/
def nativeHigherProjectionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Y.Modules) [N.IsInvertible] (G : X.Modules) (q : ℕ) :
    (Scheme.Modules.higherDirectImage f q).obj ((Scheme.Modules.pullback f).obj N ⊗ G) ≅
      N ⊗ (Scheme.Modules.higherDirectImage f q).obj G := by
  let F := Scheme.Modules.pushforward f
  let L := (Scheme.Modules.pullback f).obj N
  let tensorTarget := tensorRight N
  let tensorSource := tensorRight L
  haveI : tensorTarget.Additive := Functor.additive_of_preserves_binary_products tensorTarget
  haveI : tensorSource.Additive := Functor.additive_of_preserves_binary_products tensorSource
  haveI : (Scheme.Modules.tensorRightEquivalence L).functor.Additive := by
    change tensorSource.Additive
    infer_instance
  haveI : tensorTarget.PreservesHomology := inferInstance
  let exactPost : tensorTarget.obj ((F.rightDerived q).obj G) ≅
      ((F ⋙ tensorTarget).rightDerived q).obj G :=
    rightDerivedPostcomposeIso F tensorTarget G q
  let derivedNatural := rightDerivedNatIsoComponent
    (F ⋙ tensorTarget) (tensorSource ⋙ F)
    (Scheme.Modules.invertibleProjectionIso f N) G q
  let exactPre : ((tensorSource ⋙ F).rightDerived q).obj G ≅
      (F.rightDerived q).obj (tensorSource.obj G) :=
    rightDerivedPrecomposeEquivalenceIso (Scheme.Modules.tensorRightEquivalence L) F G q
  exact (Scheme.Modules.higherDirectImage f q).mapIso (β_ L G) ≪≫
    (exactPost ≪≫ derivedNatural ≪≫ exactPre).symm ≪≫
      β_ ((Scheme.Modules.higherDirectImage f q).obj G) N

/-- Lower higher-direct-image vanishing is preserved by tensoring with the
actual pullback of an invertible target coefficient. -/
theorem isZero_higherDirectImage_tensorPullback_of_isZero
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) [N.IsInvertible]
    (G : X.Modules) (j : ℕ) (hG : IsZero ((Scheme.Modules.higherDirectImage f j).obj G)) :
    IsZero ((Scheme.Modules.higherDirectImage f j).obj
      ((Scheme.Modules.pullback f).obj N ⊗ G)) := by
  exact IsZero.of_iso ((tensorLeft N).map_isZero hG)
    (nativeHigherProjectionIso f N G j)

end ZInQ.Contrib.CloudR2Poincare.L5
