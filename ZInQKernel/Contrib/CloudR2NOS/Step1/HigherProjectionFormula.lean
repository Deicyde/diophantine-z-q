/-
v2 (R1 v2; v1 a2746f2e is in history/): `RelativeVanishingSectionsCore` additionally assumes
`[IsSeparated fX] [IsProper fX]` and finitely presented `F`, matching ShearVanishing v2.
H5 lane3 Step 1, R1 component: the higher projection formula (PROVED) and R1a reduced to its
base-change core. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

`higherDirectImageTensorPullbackIso`: for an invertible `G`,
`R^q f_*(ℱ ⊗ f^*G) ≅ (R^q f_* ℱ) ⊗ G`, in every degree.
It is built only from published fork W07 pieces, exactly in the pattern of W07's own
`higherDirectImagePullbackIsoRestrict`:
* `Functor.compRightDerivedObjIso`, for the exact equivalence `tensorRight (f^*G)`; injectives go
  to injectives, which are `f_*`-acyclic;
* `Functor.rightDerivedObjIsoOfIso`, along W07's degree-0 `invertibleProjectionIso`;
* `Functor.rightDerivedCompObjIso`, for the exact `tensorRight G`.

R1a (ShearVanishing.lean) is PROVED from this and ONE core gap, `RelativeVanishingSectionsCore`.
That core and R1b remain UNPROVED. Both follow from field flat base change for the universal
finite free model, W07 `exists_isFiniteFreeComplex_higherDirectImage`: over `Spec K` the model
splits, so `R^q pr₂_*(pr₁^*F) ≅ O_Y^{h^q(X,F)}`, and `Γ` of a finite sum is the sum of the `Γ`s.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.ShearVanishing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ProjectionFormula
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorEquivalence
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Composition
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Abelian.RightDerived.Composition

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- The higher projection formula for an invertible module. -/
noncomputable def higherDirectImageTensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasInjectiveResolutions X.Modules] (G : Y.Modules) [G.IsInvertible] (ℱ : X.Modules)
    (q : ℕ) :
    (higherDirectImage f q).obj (ℱ ⊗ (Scheme.Modules.pullback f).obj G) ≅
      (higherDirectImage f q).obj ℱ ⊗ G :=
  (Functor.compRightDerivedObjIso (tensorRight ((Scheme.Modules.pullback f).obj G))
      (Scheme.Modules.pushforward f)
      (fun I _ q' => Functor.isZero_rightDerived_obj_injective_succ _ q' _) q ℱ).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (invertibleProjectionIso f G).symm q ℱ ≪≫
      Functor.rightDerivedCompObjIso (Scheme.Modules.pushforward f) (tensorRight G) q ℱ

/-- Core of R1a (UNPROVED; true by field flat base change, see header). -/
def RelativeVanishingSectionsCore : Prop :=
  ∀ {K : Type u} [Field K] {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) [QuasiCompact fX] [QuasiSeparated fX] [IsSeparated fX]
    [IsProper fX] [CompactSpace Y]
    [HasInjectiveResolutions (Limits.pullback fX fY).Modules]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (G : Y.Modules) [G.IsInvertible]
    (q : ℕ),
    Subsingleton (G.H 0) →
      Subsingleton (((higherDirectImage (pullback.snd fX fY) q).obj
        ((Scheme.Modules.pullback (pullback.fst fX fY)).obj F) ⊗ G).H 0)

/-- R1a, PROVED from the higher projection formula and its core. -/
theorem relativeVanishingSections (hcore : RelativeVanishingSectionsCore.{u}) :
    RelativeVanishingSections.{u} := by
  intro K _ X Y fX fY _ _ _ _ _ _ F _ _ G _ q hG
  have h := hcore fX fY F G q hG
  exact (H.mapLinearEquiv (higherDirectImageTensorPullbackIso (pullback.snd fX fY) G
    ((Scheme.Modules.pullback (pullback.fst fX fY)).obj F) q) 0).toEquiv.subsingleton

end ZInQ.Contrib.CloudR2NOS.Step1
