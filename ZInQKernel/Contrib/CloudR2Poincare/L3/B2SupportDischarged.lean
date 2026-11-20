import ZInQKernel.Contrib.CloudR2Poincare.L3.B2LerayUse
import ZInQKernel.Contrib.CloudR2Poincare.L4.FiniteSupport

/-! The finite-support cohomology and Leray assumptions are BOTH discharged by
actual native proofs. Only actual p1 vanishing / p2 support data remain in this
auxiliary reduction; they are not declared as a B2 theorem. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L3
universe u

/-- Native two-projection vanishing reduction without a finite-support or Leray input. -/
theorem higherDirectImages_snd_zero_of_fst_zero_supported
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (F : (B.X ⊗ B.X).left.Modules) [F.IsQuasicoherent]
    (hfst : ∀ j : ℕ, IsZero ((Scheme.Modules.higherDirectImage (fst B.X B.X).left j).obj F))
    (S : Set B.X.left) (hS : S.Finite) (hClosed : ∀ y ∈ S, IsClosed ({y} : Set B.X.left))
    (hsupport : ∀ j : ℕ, ∀ y : B.X.left, y ∉ S →
      Subsingleton (((Scheme.Modules.higherDirectImage (snd B.X B.X).left j).obj F).presheaf.stalk y)) :
    ∀ i : ℕ, IsZero ((Scheme.Modules.higherDirectImage (snd B.X B.X).left i).obj F) :=
  higherDirectImages_snd_zero_of_fst_zero_finite_support L4.FiniteSupportCohomology_proof
    B F hfst S hS hClosed hsupport

end ZInQ.Contrib.CloudR2Poincare.L3
