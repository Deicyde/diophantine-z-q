import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveNonvanishing

/-!
# Five-torsion logarithmic-derivative definitions

This is the actual theta-quotient candidate for the weight-one construction.
Its denominator is nonzero at every admissible torsion point. Defining the
function does NOT yet prove modularity, its Fourier expansion or the Hecke
rationality leaf.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsion

open Complex UpperHalfPlane
open scoped UpperHalfPlane

/-- The argument of theta-three representing odd theta at five-torsion. -/
def shiftedPoint (a b : ℤ) (τ : ℍ) : ℂ :=
  ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / 5 + ((τ : ℂ) + 1) / 2

/-- The completed odd-theta logarithmic derivative, expressed in Mathlib's
actual theta-three normalization. No modular-form status is assumed. -/
def torsionLogDerivative (a b : ℤ) (τ : ℍ) : ℂ :=
  (a : ℂ) / 5 + 1 / 2 +
    jacobiTheta₂' (shiftedPoint a b τ) (τ : ℂ) /
      (2 * (Real.pi : ℂ) * Complex.I * jacobiTheta₂ (shiftedPoint a b τ) (τ : ℂ))

/-- The quotient denominator is genuinely nonzero, by the closed
five-torsion nonvanishing theorem. -/
theorem denominator_ne_zero (τ : ℍ) (a b : ℤ) (h : ¬ (5 ∣ a ∧ 5 ∣ b)) :
    2 * (Real.pi : ℂ) * Complex.I * jacobiTheta₂ (shiftedPoint a b τ) (τ : ℂ) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero)
    (ThetaFive.jacobiTheta₂_fiveTorsion_ne_zero τ a b h)

end ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsion
