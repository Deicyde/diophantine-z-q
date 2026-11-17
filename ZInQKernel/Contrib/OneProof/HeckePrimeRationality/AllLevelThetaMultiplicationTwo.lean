import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelCompletedTheta
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaZeroSet
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.QuasiThetaMultiplicationTwo

/-!
# Two-division multiplication of the actual completed theta function

The independent entire-function theorem is bound here to the actual theta
function. Its global zero set and nonzero origin derivative are proved,
not supplied as hypotheses. The identity includes lattice zeros. This does
not assert torsion distribution, Eisenstein trace closure or spanning.
-/

noncomputable section
set_option autoImplicit false

open Complex
open scoped Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.CompletedTheta

/-- The actual completed theta function vanishes exactly on its lattice. -/
theorem H_zero_iff_lattice (τ : ℍ) (z : ℂ) :
    H τ z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ) := by
  change cexp (π * I * z) * jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ = 0 ↔ _
  rw [mul_eq_zero]
  simp only [Complex.exp_ne_zero, false_or]
  rw [AllLevelThetaZeroSet.jacobiTheta₂_shift_eq_zero_iff]
  constructor
  · rintro ⟨m, n, hz⟩
    exact ⟨n, m, hz.trans (by ring)⟩
  · rintro ⟨m, n, hz⟩
    exact ⟨n, m, hz.trans (by ring)⟩

/-- The actual origin zero is simple; the exponential completion has value one there. -/
theorem deriv_H_zero_ne_zero (τ : ℍ) : deriv (H τ) 0 ≠ 0 := by
  rw [deriv_H]
  have h0 := AllLevelThetaZeroSet.jacobiTheta₂_half_shift_eq_zero τ.im_pos
  simpa [Hder, h0] using AllLevelThetaZeroSet.jacobiTheta₂'_half_shift_ne_zero τ

/-- The complete actual two-division identity, with no analytic property or
multiplication identity left as a caller premise. -/
theorem H_multiplication_two (τ : ℍ) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      (∏ r : Fin 2, ∏ s : Fin 2,
        H τ (z + ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / 2)) =
          C * cexp (-2 * (π : ℂ) * I * z) * H τ (2 * z) := by
  exact QuasiThetaMultiplicationTwo.multiplication_two_explicit τ (H τ)
    (differentiable_H τ) (H_add_one τ)
    (fun z => by simpa only [neg_mul, mul_assoc] using H_add_tau τ z)
    (H_zero_iff_lattice τ) (deriv_H_zero_ne_zero τ)

end ZInQ.Contrib.HeckePrimeRationality.CompletedTheta
