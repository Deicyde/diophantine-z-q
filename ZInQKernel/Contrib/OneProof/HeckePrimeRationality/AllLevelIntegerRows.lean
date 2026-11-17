import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalCoefficients
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionForms

/-!
# Integer labels for principal-level torsion coefficients

Reduction of the first coordinate modulo the positive level transfers the
normalized-row coefficient arithmetic to every admissible integer row.
The actual functions and their period-N expansions are unchanged by this
reduction, by the proved torsion translation law.
-/

noncomputable section

open UpperHalfPlane
open ZInQ.Contrib.HeckePrimeRationality.Torsion
open ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients (zetaInField)

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelIntegerRows

variable (N : ℕ) [NeZero N]

lemma normal_good (A b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ A ∧ (N : ℤ) ∣ b)) :
    ¬ ((N : ℤ) ∣ A % (N : ℤ) ∧ (N : ℤ) ∣ b) := by
  rintro ⟨ha, hb⟩
  apply hg
  refine ⟨?_, hb⟩
  have he : A = A % (N : ℤ) + (N : ℤ) * (A / (N : ℤ)) :=
    (Int.emod_add_mul_ediv A (N : ℤ)).symm
  rw [he]
  exact dvd_add ha (dvd_mul_right _ _)

lemma torsion_eq_normal (A b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ A ∧ (N : ℤ) ∣ b)) :
    torsionLogDerivative N A b = torsionLogDerivative N (A % (N : ℤ)) b := by
  ext τ
  have hgood : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good N
      (A % (N : ℤ), b) := normal_good N A b hg
  have h := ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.F_shift (NeZero.pos N)
    hgood (A / (N : ℤ)) 0 τ
  have he : A % (N : ℤ) + (N : ℤ) * (A / (N : ℤ)) = A :=
    Int.emod_add_mul_ediv A (N : ℤ)
  simpa only [he, mul_zero, add_zero,
    ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.F] using h

/-- Actual period-N coefficient membership for every admissible integer torsion row. -/
theorem torsion_coeff_mem (A b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ A ∧ (N : ℤ) ∣ b)) (n : ℕ) :
    (qExpansion (N : ℝ) (torsionLogDerivative N A b)).coeff n ∈ coefficientField N := by
  rw [torsion_eq_normal N A b hg]
  apply ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalCoefficients.torsion_coeff_mem_int
    N (A % (N : ℤ)) b
  · exact Int.emod_nonneg _ (by exact_mod_cast NeZero.ne N)
  · exact Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos N)
  · exact normal_good N A b hg

lemma transformed_good (A b t : ℤ)
    (hg : ¬ ((N : ℤ) ∣ A ∧ (N : ℤ) ∣ b))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) :
    ¬ ((N : ℤ) ∣ A ∧ (N : ℤ) ∣ t * b) := by
  rintro ⟨ha, hb⟩
  have hnot : ¬ (N : ℤ) ∣ b := fun h => hg ⟨ha, h⟩
  exact ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.automorphism_admissible
    N b t hnot σ hσ hb

/-- Coefficientwise Galois covariance for every admissible integer row at the same actual period N. -/
theorem torsion_coeff_galois (A b t : ℤ)
    (hg : ¬ ((N : ℤ) ∣ A ∧ (N : ℤ) ∣ b))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (n : ℕ) :
    ((σ ⟨(qExpansion (N : ℝ) (torsionLogDerivative N A b)).coeff n,
        torsion_coeff_mem N A b hg n⟩ : coefficientField N) : ℂ) =
      (qExpansion (N : ℝ) (torsionLogDerivative N A (t * b))).coeff n := by
  have hA0 : 0 ≤ A % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast NeZero.ne N)
  have hAN : A % (N : ℤ) < N := Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos N)
  have hg' := normal_good N A b hg
  have hcoef : (⟨(qExpansion (N : ℝ) (torsionLogDerivative N A b)).coeff n,
      torsion_coeff_mem N A b hg n⟩ : coefficientField N) =
      ⟨(qExpansion (N : ℝ) (torsionLogDerivative N (A % (N : ℤ)) b)).coeff n,
        ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalCoefficients.torsion_coeff_mem_int
          N (A % (N : ℤ)) b hA0 hAN hg' n⟩ := by
    apply Subtype.ext
    change (qExpansion (N : ℝ) (torsionLogDerivative N A b)).coeff n =
      (qExpansion (N : ℝ) (torsionLogDerivative N (A % (N : ℤ)) b)).coeff n
    rw [torsion_eq_normal N A b hg]
  rw [hcoef, torsion_eq_normal N A (t * b) (transformed_good N A b t hg σ hσ)]
  exact ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalCoefficients.torsion_coeff_galois_int
    N (A % (N : ℤ)) b t hA0 hAN hg' σ hσ n

end ZInQ.Contrib.HeckePrimeRationality.AllLevelIntegerRows
