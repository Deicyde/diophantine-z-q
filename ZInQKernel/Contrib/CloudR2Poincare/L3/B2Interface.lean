import ZInQKernel.Contrib.CloudR2Poincare.L1.PicardKernel
import ZInQKernel.Contrib.CloudR2Poincare.L1.PicardZeroH0
import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmple
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-!
# B2 native interfaces

These are ordinary labelled propositions, NOT instances or assumed Facts.
B1 and Leray remain undischarged inputs until a proof is supplied. The B2
output is native Picard point-surjectivity, not representability or universality.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L3

universe u

/-- Literal invariance of an actual Picard class under all rational translations. -/
def TranslationInvariant {k : Type u} [Field k] (B : PkgI3.AbVar k)
    (N : B.X.left.Pic) : Prop :=
  ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X,
    Scheme.Pic.map (L1.translate B.X b).left N = N

/-- B1, in the actual native `.H q` model. This proposition is not yet proved. -/
def NativePicZeroVanishing : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (N : B.X.left.Modules) [N.IsInvertible],
    TranslationInvariant B (Scheme.Pic.mk N) → Scheme.Pic.mk N ≠ 1 →
      ∀ q : ℕ, Subsingleton (N.H q)

/-- The agreed B2 output, using actual invertible representatives of Picard classes. -/
def PicZeroPointSurjectivity : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (M N : B.X.left.Modules)
    [M.IsInvertible] [N.IsInvertible],
    L2.VeryAmple B.X.hom M → TranslationInvariant B (Scheme.Pic.mk N) →
      ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X,
        Scheme.Pic.mk N = L1.translationClass B.X (Scheme.Pic.mk M) b

/-- ONE labelled Leray degeneration input covering both projections of B×B.
The proper/qcqs hypotheses are supplied intrinsically by the actual abelian
variety. This is not proved merely by an affine Čech Leray theorem. -/
def NativeLerayDegeneration : Prop :=
  ∀ (k : Type u) [Field k] (B : PkgI3.AbVar k)
    (F : (B.X ⊗ B.X).left.Modules) [F.IsQuasicoherent]
    (f : (B.X ⊗ B.X).left ⟶ B.X.left),
    (f = (fst B.X B.X).left ∨ f = (snd B.X B.X).left) →
    (∀ (j p : ℕ), 0 < p →
      Subsingleton (((Scheme.Modules.higherDirectImage f j).obj F).H p)) →
    ∀ i : ℕ, Nonempty (F.H i ≃+
      (((Scheme.Modules.higherDirectImage f i).obj F).H 0))

/-- ONE further labelled input: native cohomology and detection for a QC sheaf
supported on a finite set of CLOSED points. F is an actual sheaf on B, not a
replacement sheaf on an unspecified finite scheme. The proof is pending. -/
def FiniteSupportCohomology : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (F : B.X.left.Modules) [F.IsQuasicoherent]
    (S : Set B.X.left), S.Finite →
    (∀ y ∈ S, IsClosed ({y} : Set B.X.left)) →
    (∀ y : B.X.left, y ∉ S → Subsingleton (F.presheaf.stalk y)) →
    (∀ p : ℕ, 0 < p → Subsingleton (F.H p)) ∧
      (Subsingleton (F.H 0) → IsZero F)

end ZInQ.Contrib.CloudR2Poincare.L3
