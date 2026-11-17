import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.QuasiThetaMultiplicationNat
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaMultiplicationTwo

/-!
# Multiplication of the actual completed theta function in every positive degree

The independently proved analytic properties of the completed theta function
are bound to the generic positive-degree theorem. No analytic premise remains
in the resulting actual identity. No trace or spanning assertion is made.
-/

noncomputable section
set_option autoImplicit false

open Complex
open scoped Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.CompletedTheta

/-- The actual completed theta multiplication identity for every positive
natural degree, including degree one and all lattice zeros. -/
theorem H_multiplication_nat (n : ℕ) (hn : 0 < n) (τ : ℍ) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      (∏ r : Fin n, ∏ s : Fin n,
        H τ (z + ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (n : ℂ))) =
          C * cexp (-(π : ℂ) * I * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) * H τ ((n : ℂ) * z) := by
  exact QuasiThetaMultiplicationNat.multiplication_nat_explicit n hn τ (H τ)
    (differentiable_H τ) (H_add_one τ)
    (fun z => by simpa only [neg_mul, mul_assoc] using H_add_tau τ z)
    (H_zero_iff_lattice τ) (deriv_H_zero_ne_zero τ)

/-- The same actual theorem with the completed function unfolded to its
exponential and Mathlib Jacobi theta expression. -/
theorem jacobiTheta₂_completed_multiplication_nat (n : ℕ) (hn : 0 < n) (τ : ℍ) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      (∏ r : Fin n, ∏ s : Fin n,
        (cexp ((π : ℂ) * I * (z + ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (n : ℂ))) *
          jacobiTheta₂
            ((z + ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (n : ℂ)) + ((τ : ℂ) + 1) / 2) τ)) =
          C * cexp (-(π : ℂ) * I * (n : ℂ) * ((n - 1 : ℕ) : ℂ) * z) *
            (cexp ((π : ℂ) * I * ((n : ℂ) * z)) *
              jacobiTheta₂ (((n : ℂ) * z) + ((τ : ℂ) + 1) / 2) τ) := by
  simpa only [H] using H_multiplication_nat n hn τ

end ZInQ.Contrib.HeckePrimeRationality.CompletedTheta
