import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaWeierstrass
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionTwoRegular

/-!
# Actual torsion values for the weight-two identities

The weight-one value is the scaled completed torsion logarithmic derivative.
The weight-two value is Mathlib's actual Weierstrass function off the zero
class, extended by zero there. The quadratic value is defined from these
actual functions. No Eisenstein membership, Fourier identity, trace closure
or spanning assertion is made by these definitions.
-/

noncomputable section
set_option autoImplicit false

open Complex UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionWeierstrassData

/-- The common weight-one normalization. -/
def scale : ℂ := -2 * (Real.pi : ℂ) * Complex.I

/-- The completed torsion value, with the established zero convention. -/
def lambdaValue (N : ℕ) (a b : ℤ) (τ : ℍ) : ℂ :=
  scale * TorsionDistributionTwo.reg N a b τ

/-- The actual Weierstrass value away from the zero torsion class. -/
def xValue (N : ℕ) (a b : ℤ) (τ : ℍ) : ℂ :=
  if (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then 0 else
    (ThetaWeierstrass.periodPair τ).weierstrassP (CompletedTheta.torsionPoint N a b τ)

/-- The quadratic torsion value, not an assumed Eisenstein series. -/
def muValue (N : ℕ) (a b : ℤ) (τ : ℍ) : ℂ :=
  (lambdaValue N a b τ ^ 2 - xValue N a b τ) / 2

lemma scale_ne_zero : scale ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

lemma lambdaValue_of_good (N : ℕ) (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    lambdaValue N a b τ = scale * Torsion.torsionLogDerivative N a b τ := by
  rw [lambdaValue, TorsionDistributionTwo.reg_of_good hg]

lemma xValue_of_good (N : ℕ) (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    xValue N a b τ =
      (ThetaWeierstrass.periodPair τ).weierstrassP (CompletedTheta.torsionPoint N a b τ) := by
  simp only [xValue, if_neg hg]

lemma lambdaValue_zero (N : ℕ) (τ : ℍ) : lambdaValue N 0 0 τ = 0 := by
  simp [lambdaValue, TorsionDistributionTwo.reg]

lemma xValue_zero (N : ℕ) (τ : ℍ) : xValue N 0 0 τ = 0 := by
  simp [xValue]

lemma muValue_zero (N : ℕ) (τ : ℍ) : muValue N 0 0 τ = 0 := by
  simp [muValue, lambdaValue_zero, xValue_zero]

end ZInQ.Contrib.HeckePrimeRationality.TorsionWeierstrassData
