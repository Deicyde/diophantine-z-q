/-
H5 Step2 / exact delegated consumer Props, edition 001.
Copyright (c) 2026 H5 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. This file names PENDING PRODUCER THEOREMS, not
Facts, axioms, typeclass witnesses or a proof of I0/I2. Each Prop must be
proved or truth-verified independently by C6 before any goal-reduction
credit. No proof-bearing assumption below may enter the original NOS input.

OWNERSHIP CUT, H5 lead 2026-11-17T04:21Z:
  C5: RegularLocalUFD, SmoothFieldStalkRegular, AffineComplementPurity,
      AffineComplementCartier, and SameAbVarAffineComplement assembly.
  C3: FiniteSupportStabilizer, FiniteSquarePresentation, NativeFBSFieldDescent.
  Lane2: interface ownership, original H(D)⊆K(M)/H(D) finite from I1,
      actual translated-section/frame/presentation and I0/I2 assemblies.
No new agent/node. No duplicate delegated core proofs in Lane2.

The received RegularLocalRing.UniqueFactorization and EffectiveCartier
AffineComplement/SeparatedAffineComplement are ATTRIBUTED BLUEPRINTS ONLY;
NO Stacks module/predicate import or Stacks↔native bridge is allowed. Native
Mathlib regular-local and W07 ideal/invertibility/module operations below
are literal original predicates. Powers are native LEFT-recursive tensorPow.
FBS/ProjPresentation use the exact historical defining namespace/fields;
default-limit Source binding is separate, not a predicate or power alias.

SAME ORIGINAL OBJECTS/APPLICATION DISCHARGES:
* I0: A = Hbar = PkgI2.baseChange Hs (AlgebraicClosure k), original transported
  group law. Choose an affine open U containing the ACTUAL group identity.
  A is proper/smooth/geometrically integral; field gives LFT/Noetherian,
  separatedness and integral/dense-U geometry. C5 proves stalk regularity,
  then regular⇒UFD, purity and native Cartier D_U with support = complement U.
  Auxiliary N_U is built from D_U on the SAME A by Lane2; it is not Ms/beta.
* I2: A = Hbar, N = literal pullback Msbar, theta = literal pulled original
  nonzero theta, D = literal Dbar comap; D.IsInvertible and N≈D.toModulesᵛ
  come from actual effectivity/flat pullback. Lane2's exact IDEAL inclusion
  turns C3's I1 output into finite H(D). Lane2 makes a native N^2 presentation
  from the actual paired sections/frames/G5; C3 proves its toProj finite.
* Descent: k is ORIGINAL residue field, K = SAME AlgebraicClosure k,
  A = original Hs, N = SAME Ms and b is SAME positive native exponent.
  The statement is generalized to any field extension, but changes no
  original field/embedding/group/module/scalar/power/presentation carrier.

TRUTH PRE-CHECKS (not independent certificates):
[A1] RegularLocalUFD: TRUE, regular local rings are factorial (Stacks
     0AFZ/0AG0, Auslander--Buchsbaum/Nagata); no dimension/CharZero cap.
     A normal or arbitrary Noetherian local ring alone need not be UFD.
[A2] SmoothFieldStalkRegular: TRUE, smooth over a regular base preserves
     regularity; every field is regular. All stalks, not only closed ones.
     LFT without smoothness permits singular/nonregular local rings.
[A3] AffineComplementPurity: TRUE, affine-complement purity (0EGJ/0BCW).
     Separated + affine U gives affine inclusion. At a generic component
     of the complement, punctured local spectrum is affine; UFD/normal
     depth excludes dimension >=2, density excludes dimension0, so dim=1.
     Removing UFD/normal-depth or density is not permitted; U may equal X,
     in which case no component/generic point is asserted to exist.
[A4] AffineComplementCartier: TRUE, the FINITE reduced codim1 prime-component
     ideals from A3 are locally principal/non-zero-divisor under stalk UFD;
     their product is native invertible and has EXACT complement support.
     Support equality is ONLY an output here, not arbitrary ideal equality.
[A5] SameAbVarAffineComplement: TRUE from A1--A4 and actual AV fields. The
     identity-containing affine open is nonempty and dense; no ample/QP,
     embedding/FBS/model/Pic0/nondegeneracy assumption is added.
[B1] FiniteSupportStabilizer: TRUE. On smooth integral Noetherian A, the SAME
     effective Cartier ideal has a FINITE positive weighted prime-component
     factorization. Support-preserving translations permute these components;
     the finite-action kernel fixes each PRIME IDEAL and every multiplicity,
     hence fixes D itself. Its kernel is in the finite IDEAL H(D), so all
     label fibres are finite cosets and the support stabilizer is finite.
     The examples (t) vs (t^2), or [0] vs 2[0], refute direct support⇒ideal
     equality; no such implication is asserted. Actual factorization and
     component/translation maps MUST be proved, not supplied as a Factory.
[B2] FiniteSquarePresentation: TRUE, Mumford §6 Application 1. Effective D
     with finite H(D) on an abelian variety has basepoint-free |2D| and its
     map is finite. ANY exact native section presentation of N^2 is finite:
     a contracted complete curve makes its N^2 restriction trivial; all
     global paired sections then restrict as proportional constants, giving
     the genuine contracted-curve/support-stabilizer contradiction with B1.
     The presentation has actual sigma/frame/ratio fields, not an arbitrary
     projective map. No-common-zero alone is insufficient: pr1-pullback of
     an ample line on E1×E2 contracts E2, but has infinite H(D) and is excluded.
     No finite=closed claim; no positive-dimension restriction on A or D.
[B3] NativeFBSFieldDescent: TRUE, flat H0 base change and fpqc descent.
     H0(N^b) is finite over k and extension gives ACTUAL H0(Nbar^b) with its
     original K-scalars. Choose k-basis, descend evaluation generation, build
     SAME positive-power full-system presentation; after extension it refines
     the finite given system and is proper/quasi-finite, hence finite. Actual
     fpqc/field-extension finiteness descent gives finite original map.
     Nothing says the arbitrary geometric sigma or its toProj itself descends;
     new original-k sigma is allowed, the ORIGINAL line/exponent is not changed.
     Picard-class/rank equality or different line/power cannot substitute for
     canonical pullback/tensor/evaluation maps. No perfectness/CharZero premise.

Native remains HELD. No compiler, parser, AST, evaluator or helper probe;
no root/loader/source-provider/cache/toolchain/base/budget/transparency change.
No H72/Stacks/fork/C3/C4/C5/protected Source edits or further intake.
-/
import NativeDivisorKernel
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces
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
    ∀ (C : irreducibleComponents ((U : Set X)ᶜ)) (x : (U : Set X)ᶜ),
      IsGenericPoint x (C : Set ((U : Set X)ᶜ)) →
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
