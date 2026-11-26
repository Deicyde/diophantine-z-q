import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelSmooth

/-! # Normality of the rational short-level quotient -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open ModelTorsion RC.ModelInvariants

open private rationalLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
open private normal_degreeZeroInvariants from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelSmooth

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

private theorem rationalCover_regular : IsRegularRing (rationalCover N) := by
  let A := ShortBase ℚ
  let S := rationalCover N
  letI : Algebra.Smooth (MvPolynomial (Fin 2) ℚ) A :=
    Algebra.Smooth.of_isLocalization_Away (shortEquation ℚ).Δ
  letI : Algebra.Smooth ℚ A := Algebra.Smooth.comp ℚ (MvPolynomial (Fin 2) ℚ) A
  letI : Algebra.Etale A S :=
    (exactOrderAlgebra_finite_etale (shortFamily ℚ) (rationalLevel_isUnit (N := N))).2
  letI : Algebra.Smooth ℚ S := Algebra.Smooth.comp ℚ A S
  exact Algebra.Smooth.isRegularRing ℚ S

/-- Every prime localization of the detector-independent quotient is a normal domain. -/
theorem Y0RationalAlgebra_normal (q : Ideal (Y0RationalAlgebra h₂)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  letI := rationalCover_regular (N := N)
  exact normal_degreeZeroInvariants (rationalGrading h₂)
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) q

#print axioms rationalCover_regular
#print axioms Y0RationalAlgebra_normal

end WeierstrassCurve.ModelLevels.ModelGeneric
