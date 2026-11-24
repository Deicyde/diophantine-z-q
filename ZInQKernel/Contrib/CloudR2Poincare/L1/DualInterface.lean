import ZInQKernel.Contrib.CloudR2Poincare.Skeleton
import ZInQKernel.Contrib.CloudR2Poincare.L1.Stabilizer
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Normalized

/-!
# Exact noncircular quotient/dual inputs for PolarizationRetract

H-72 round 2, L1. The structures in this file STATE the geometric data still
required from the quotient construction; they do not assert that such data
exist, install any Fact, or supply an unconditional dual-existence theorem.

Milne AVs (2022 transcription), §§9–10 pp.15–17:
* Pic⁰ consists of translation-invariant classes (Proposition 9.2), not the
  cohomological degree-zero part on a higher-dimensional variety.
* The actual dual has a normalized universal invertible sheaf and dim A∨=dim A.
* In characteristic zero one constructs it as A/K(L), descends the normalized
  polarization bundle, and proves its universal property using the graph of a
  triviality locus and ZMT. The graph/universal-property step is not provided
  merely by the existence of a finite-flat quotient.

The final theorem below is ONLY the per-embedding assembly from actual dual
maps, their restriction identity, and L2's actual isogeny statement. Its exact
conditional type is kept visible; it is not PolarizationRetract_proof.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

/-- Spec Ω as a test scheme over k (the same object used for PkgI3 points). -/
def fieldTest (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- The zero section of an abelian variety lies over its base. -/
theorem abVarUnit_over {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k) :
    η[A.X].left ≫ A.X.hom = 𝟙 (Spec (.of k)) := by
  simpa using Over.w η[A.X]

/-- Normalization of a line-bundle class along the zero section. -/
def IsNormalizedFamily {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k)
    (T : Over (Spec (.of k))) (M : (pullback A.X.hom T.hom).Pic) : Prop :=
  Pic.map (sectionBaseChange A.X.hom η[A.X].left (abVarUnit_over A) T) M = 1

/-- The genuine fibrewise Pic⁰ condition: every field fibre is translation invariant.
This deliberately does not use χ(M)-χ(O)=0. -/
def IsPicardZeroFamily {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k)
    (T : Over (Spec (.of k))) (M : (pullback A.X.hom T.hom).Pic) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] (t : fieldTest k Ω ⟶ T)
    (a : fieldTest k Ω ⟶ A.X),
    Pic.map (familyTranslate A.X a).left
        (Pic.map (JacobianChallenge.baseChangeMap A.X.hom t) M) =
      Pic.map (JacobianChallenge.baseChangeMap A.X.hom t) M

/-- The exact general dual/universal-Poincare data the quotient must eventually supply.
This is a data type, NOT an assumed existence Fact. -/
structure DualPresentation {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k) where
  dual : _root_.PkgI3.AbVar k
  poincare : (pullback A.X.hom dual.X.hom).Modules
  [invertible : poincare.IsInvertible]
  normalized : IsNormalizedFamily A dual.X (Pic.mk poincare)
  picardZero : IsPicardZeroFamily A dual.X (Pic.mk poincare)
  atZero : Pic.map (JacobianChallenge.baseChangeMap A.X.hom η[dual.X]) (Pic.mk poincare) = 1
  universal : ∀ (T : Over (Spec (.of k))) (M : (pullback A.X.hom T.hom).Pic),
    IsNormalizedFamily A T M → IsPicardZeroFamily A T M →
    ∃! x : T ⟶ dual.X,
      Pic.map (JacobianChallenge.baseChangeMap A.X.hom x) (Pic.mk poincare) = M
  dim_eq : dual.dim = A.dim

attribute [instance] DualPresentation.invertible

/-- An actual finite subgroup SCHEME realizing K(L) on algebraically closed field points.
The existence of this record is not inferred from a finite point set. -/
structure FiniteStabilizerScheme {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k)
    (L : A.X.left.Pic) where
  K : Over (Spec (.of k))
  [grp : GrpObj K]
  j : K ⟶ A.X
  [monHom : IsMonHom j]
  [closed : IsClosedImmersion j.left]
  [finite : IsFinite K.hom]
  points : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω],
    Set.range (fun a : fieldTest k Ω ⟶ K ↦ a ≫ j) =
      (stabilizerSubgroup A.X L (fieldTest k Ω) : Set (fieldTest k Ω ⟶ A.X))

attribute [instance] FiniteStabilizerScheme.grp FiniteStabilizerScheme.monHom
  FiniteStabilizerScheme.closed FiniteStabilizerScheme.finite

/-- The actual finite-flat quotient output needed from Stacks 07S6.
The target is merely a scheme over k; abelian-variety geometry is another proof step. -/
structure StabilizerQuotient {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k)
    (L : A.X.left.Pic) (H : FiniteStabilizerScheme A L) where
  Q : Over (Spec (.of k))
  q : A.X ⟶ Q
  [flat : Flat q.left]
  [finite : IsFinite q.left]
  [surjective : Surjective q.left]
  [finitePresentation : LocallyOfFinitePresentation q.left]
  kernelPair : IsPullback ((fst H.K A.X ≫ H.j) * snd H.K A.X) (snd H.K A.X) q q

attribute [instance] StabilizerQuotient.flat StabilizerQuotient.finite
  StabilizerQuotient.surjective StabilizerQuotient.finitePresentation

/-- The exact isogeny/dimension assembly expected from the dual and positivity lanes.
No desired dual-existence, representability, or PolarizationRetract Fact is assumed. -/
theorem polarization_witness_of_dual_maps
    {k : Type} [Field k] [CharZero k] (J B : _root_.PkgI3.AbVar k)
    (i : _root_.PkgI3.AbVar.Hom B J)
    (JDual : DualPresentation J) (BDual : DualPresentation B)
    (φL : _root_.PkgI3.AbVar.Hom J JDual.dual)
    (iDual : _root_.PkgI3.AbVar.Hom JDual.dual BDual.dual)
    (φM : _root_.PkgI3.AbVar.Hom B BDual.dual)
    (hrestriction : i.hom ≫ φL.hom ≫ iDual.hom = φM.hom)
    (hisogeny : _root_.PkgI3.AbVar.IsIsogenyMor φM.hom) :
    ∃ (D : _root_.PkgI3.AbVar k) (φ : _root_.PkgI3.AbVar.Hom J D),
      _root_.PkgI3.AbVar.IsIsogenyMor (i.hom ≫ φ.hom) ∧ D.dim ≤ B.dim := by
  let φ : _root_.PkgI3.AbVar.Hom J BDual.dual :=
    _root_.PkgI3.AbVar.Hom.mk' (φL.hom ≫ iDual.hom)
  refine ⟨BDual.dual, φ, ?_, BDual.dim_eq.le⟩
  change _root_.PkgI3.AbVar.IsIsogenyMor (i.hom ≫ φL.hom ≫ iDual.hom)
  rw [hrestriction]
  exact hisogeny

end ZInQ.Contrib.CloudR2Poincare.L1
