/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Native interfaces for divisor and finite-section constructions

These propositions retain the original fields, group objects, stalks,
Cartier ideals, line bundles and tensor powers. Complement components and
their generic points are taken in the closed-complement subtype; dimension
is measured on the stalk of the original scheme.

Each interface is an intermediate proposition whose hypotheses and actual
native maps must be supplied. The finite-section descent keeps the same
line and positive exponent; no model, line or support-to-ideal replacement
is encoded.
-/
import ZInQKernel.Contrib.CMSerreTateSupport.NativeDivisorKernel
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
  MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.Step2DelegatedInterfaces

/-! ### C5: native regular/UFD/purity/Cartier producers -/

/-- A1, native Mathlib regular-local predicate, including its local and
Noetherian fields. Produce the UFD structure, not a Factory assumption. -/
def RegularLocalUFD : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], UniqueFactorizationMonoid R

/-- A2, native geometry adapter: every ACTUAL stalk of a smooth field scheme
is regular local. This is the hypothesis that I0 itself must discharge. -/
def SmoothFieldStalkRegular : Prop :=
  ∀ {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X),
    IsRegularLocalRing (X.presheaf.stalk x)

/-- A3, native purity: components and generic points live in the ACTUAL
closed complement subtype, but the dimension is of the ORIGINAL X stalk.
All hypotheses are derived for I0's same Hbar, not added to NOS. -/
def AffineComplementPurity : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X] [Scheme.IsSeparated X]
    (U : X.Opens) (_ : IsAffineOpen U) (_ : Dense (U : Set X)),
    (∀ x : X, x ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk x)) →
    ∀ (C : irreducibleComponents ((U : Set X)ᶜ : Set X)) (x : ((U : Set X)ᶜ : Set X)),
      IsGenericPoint x (C : Set ((U : Set X)ᶜ : Set X)) →
      ringKrullDim (X.presheaf.stalk (x : X)) = 1

/-- A4, ACTUAL native ideal and invertibility; no Stacks effective-Cartier
predicate, no support-to-ideal inference. U=X yields the native unit ideal. -/
def AffineComplementCartier : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X] [Scheme.IsSeparated X]
    (U : X.Opens) (_ : IsAffineOpen U) (_ : Dense (U : Set X)),
    (∀ x : X, x ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk x)) →
    ∃ (D : X.IdealSheafData), D.IsInvertible ∧ (D.support : Set X) = (U : Set X)ᶜ

/-- A5, exact C5 consumer-ready specialization. SAME A, SAME affine U and
original identity point. C5 derives EVERY regular/UFD/purity hypothesis;
Lane2 constructs the auxiliary divisor line/section and applies App.1. -/
def SameAbVarAffineComplement : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (U : A.X.left.Opens) (_ : IsAffineOpen U)
    (_ : (η[A.X]).left (IsLocalRing.closedPoint K) ∈ U),
    ∃ (D : A.X.left.IdealSheafData), D.IsInvertible ∧
      (D.support : Set A.X.left) = (U : Set A.X.left)ᶜ

/-! ### C3: finite square map including multiplicities; same-power field descent -/

/-- B1, exact missing support/IDEAL bridge. Only finiteness is concluded:
individual support-preserving translations NEED NOT preserve D itself.
C3 must produce the native prime-component/multiplicity and finite-action
argument, without support-equality, Cartier/rank or stabilizer Fact. -/
def FiniteSupportStabilizer : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData) (_ : D.IsInvertible),
    (H5OriginalDVR.Lane2.NativeDivisorKernel.divisorStabilizer A D).Finite →
    {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X |
      (D.comap (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x)).support =
        D.support}.Finite

/-- B2, exact C3 finite-map consumer. A/N/theta/D are the SAME geometric
pullbacks of the original special-fibre data. The premise H(D).Finite is
Lane2's OUTPUT from I1 and its genuine IDEAL inclusion, not a new NOS input.
Lane2 supplies the actual N^2 presentation; C3 proves ITS map finite. -/
def FiniteSquarePresentation : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N) (_ : θ ≠ 0)
    (D : A.X.left.IdealSheafData) (_ : D.IsInvertible)
    (_ : D = θ.zeroLocus) (_ : Nonempty (N ≅ D.toModulesᵛ)),
    (H5OriginalDVR.Lane2.NativeDivisorKernel.divisorStabilizer A D).Finite →
    ∀ (d : ℕ)
      (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
        (Scheme.Modules.tensorPow N 2) A.X.hom d), IsFinite 𝔓.toProj

/-- B3, field-descent consumer: SAME original N, literal base-change Nbar,
SAME positive native exponent b. The geometric presentation is allowed to
be replaced by ORIGINAL-k sections, never by a different line or power.
C3 proves actual H0/evaluation and finite-map descent, not a PB/power alias. -/
def NativeFBSFieldDescent : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible] (b : ℕ) (_ : 0 < b),
    let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Abar := PkgI2.baseChange A K
    let Nbar : Abar.X.left.Modules :=
      (Scheme.Modules.pullback (pullback.fst A.X.hom g)).obj N
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
      (R := K) (Scheme.Modules.tensorPow Nbar b) Abar.X.hom →
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
      (R := k) (Scheme.Modules.tensorPow N b) A.X.hom

end H5OriginalDVR.Lane2.Step2DelegatedInterfaces
