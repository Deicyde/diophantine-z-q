import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveNormalizedGenerators
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveCyclotomicField

/-!
# Rationality of the concrete normalized level-five generators

The two generators are the actual torsion-theta modular forms. Coefficientwise
Galois conjugation is constructed only from their explicit cyclotomic linear
combinations. Their rational leading coefficients and the sharp weight-one
bound make those conjugates equal to the original forms. No general arithmetic
q-structure or Hecke rationality statement is assumed.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality.NormalizedFive

open ThetaFiveTorsion ThetaFiveTorsionCoefficients ThetaFiveCyclotomicField

/-- The constant and first coefficients evaluated inside the actual field. -/
def cInField (b : ℤ) : KFive := (wInField b + 1) / (2 * (wInField b - 1))
def dInField (b : ℤ) : KFive := (wInField b)⁻¹ - wInField b

lemma cInField_coe (b : ℤ) : (cInField b : ℂ) = c b := by
  change ((wInField b : ℂ) + 1) / (2 * ((wInField b : ℂ) - 1)) = c b
  rw [wInField_coe]
  rfl

lemma dInField_coe (b : ℤ) : (dInField b : ℂ) = d b := by
  change (wInField b : ℂ)⁻¹ - (wInField b : ℂ) = d b
  rw [wInField_coe]
  rfl

/-- Exact coefficient lifts of the concrete generators. -/
def aCoefficient (n : ℕ) : KFive :=
  2 * cInField 2 * coefficientInField 1 n - 2 * cInField 1 * coefficientInField 2 n

def bCoefficient (n : ℕ) : KFive :=
  -2 * dInField 2 * coefficientInField 1 n + 2 * dInField 1 * coefficientInField 2 n

lemma aCoefficient_coe (n : ℕ) : (aCoefficient n : ℂ) = coefficient 1 n A := by
  change 2 * (cInField 2 : ℂ) * (coefficientInField 1 n : ℂ) -
    2 * (cInField 1 : ℂ) * (coefficientInField 2 n : ℂ) = coefficient 1 n A
  rw [cInField_coe, cInField_coe, coefficientInField_coe 1 (by decide),
    coefficientInField_coe 2 (by decide)]
  simp only [A, map_sub, map_smul, smul_eq_mul]
  rfl

lemma bCoefficient_coe (n : ℕ) : (bCoefficient n : ℂ) = coefficient 1 n B := by
  change -2 * (dInField 2 : ℂ) * (coefficientInField 1 n : ℂ) +
    2 * (dInField 1 : ℂ) * (coefficientInField 2 n : ℂ) = coefficient 1 n B
  rw [dInField_coe, dInField_coe, coefficientInField_coe 1 (by decide),
    coefficientInField_coe 2 (by decide)]
  simp only [B, map_add, map_smul, smul_eq_mul]
  rfl

lemma aCoefficient_zero : aCoefficient 0 = 0 := by
  apply Subtype.ext
  change (aCoefficient 0 : ℂ) = 0
  rw [aCoefficient_coe, A_coeff_zero]

lemma aCoefficient_one : aCoefficient 1 = 1 := by
  apply Subtype.ext
  change (aCoefficient 1 : ℂ) = 1
  rw [aCoefficient_coe, A_coeff_one]

lemma bCoefficient_zero : bCoefficient 0 = 1 := by
  apply Subtype.ext
  change (bCoefficient 0 : ℂ) = 1
  rw [bCoefficient_coe, B_coeff_zero]

lemma bCoefficient_one : bCoefficient 1 = 0 := by
  apply Subtype.ext
  change (bCoefficient 1 : ℂ) = 0
  rw [bCoefficient_coe, B_coeff_one]

/-- The actual modular form obtained by conjugating the explicit field
scalars and the torsion labels; no pointwise automorphism of complex values. -/
def galoisA (σ : KFive ≃ₐ[ℚ] KFive) (t : ℤ)
    (hσ : σ zetaInField = zetaInField ^ t) : MF 1 :=
  (2 * (σ (cInField 2) : ℂ)) •
      torsionForm (t * 1) (automorphism_admissible 1 t (by decide) σ hσ) -
    (2 * (σ (cInField 1) : ℂ)) •
      torsionForm (t * 2) (automorphism_admissible 2 t (by decide) σ hσ)

def galoisB (σ : KFive ≃ₐ[ℚ] KFive) (t : ℤ)
    (hσ : σ zetaInField = zetaInField ^ t) : MF 1 :=
  (-2 * (σ (dInField 2) : ℂ)) •
      torsionForm (t * 1) (automorphism_admissible 1 t (by decide) σ hσ) +
    (2 * (σ (dInField 1) : ℂ)) •
      torsionForm (t * 2) (automorphism_admissible 2 t (by decide) σ hσ)

lemma coefficient_galoisA (σ : KFive ≃ₐ[ℚ] KFive) (t : ℤ)
    (hσ : σ zetaInField = zetaInField ^ t) (n : ℕ) :
    coefficient 1 n (galoisA σ t hσ) = (σ (aCoefficient n) : ℂ) := by
  have hmap : σ (aCoefficient n) =
      2 * σ (cInField 2) * coefficientInField (t * 1) n -
        2 * σ (cInField 1) * coefficientInField (t * 2) n := by
    simp only [aCoefficient, map_sub, map_mul, map_ofNat]
    rw [coefficientInField_galois 1 t (by decide) σ hσ,
      coefficientInField_galois 2 t (by decide) σ hσ]
  rw [hmap]
  change coefficient 1 n (galoisA σ t hσ) =
    2 * (σ (cInField 2) : ℂ) * (coefficientInField (t * 1) n : ℂ) -
      2 * (σ (cInField 1) : ℂ) * (coefficientInField (t * 2) n : ℂ)
  simp only [galoisA, map_sub, map_smul, smul_eq_mul, coefficient_torsion]
  rw [coefficientInField_coe (t * 1) (automorphism_admissible 1 t (by decide) σ hσ),
    coefficientInField_coe (t * 2) (automorphism_admissible 2 t (by decide) σ hσ)]

lemma coefficient_galoisB (σ : KFive ≃ₐ[ℚ] KFive) (t : ℤ)
    (hσ : σ zetaInField = zetaInField ^ t) (n : ℕ) :
    coefficient 1 n (galoisB σ t hσ) = (σ (bCoefficient n) : ℂ) := by
  have hmap : σ (bCoefficient n) =
      -2 * σ (dInField 2) * coefficientInField (t * 1) n +
        2 * σ (dInField 1) * coefficientInField (t * 2) n := by
    simp only [bCoefficient, map_add, map_mul, map_neg, map_ofNat]
    rw [coefficientInField_galois 1 t (by decide) σ hσ,
      coefficientInField_galois 2 t (by decide) σ hσ]
  rw [hmap]
  change coefficient 1 n (galoisB σ t hσ) =
    -2 * (σ (dInField 2) : ℂ) * (coefficientInField (t * 1) n : ℂ) +
      2 * (σ (dInField 1) : ℂ) * (coefficientInField (t * 2) n : ℂ)
  simp only [galoisB, map_add, map_smul, smul_eq_mul, coefficient_torsion]
  rw [coefficientInField_coe (t * 1) (automorphism_admissible 1 t (by decide) σ hσ),
    coefficientInField_coe (t * 2) (automorphism_admissible 2 t (by decide) σ hσ)]

lemma galoisA_eq_self (σ : KFive ≃ₐ[ℚ] KFive) (t : ℤ)
    (hσ : σ zetaInField = zetaInField ^ t) : galoisA σ t hσ = A := by
  apply eq_of_first_two
  · rw [coefficient_galoisA, aCoefficient_zero, map_zero, A_coeff_zero]
    rfl
  · rw [coefficient_galoisA, aCoefficient_one, map_one, A_coeff_one]
    rfl

lemma galoisB_eq_self (σ : KFive ≃ₐ[ℚ] KFive) (t : ℤ)
    (hσ : σ zetaInField = zetaInField ^ t) : galoisB σ t hσ = B := by
  apply eq_of_first_two
  · rw [coefficient_galoisB, bCoefficient_zero, map_one, B_coeff_zero]
    rfl
  · rw [coefficient_galoisB, bCoefficient_one, map_zero, B_coeff_one]
    rfl

lemma aCoefficient_fixed (n : ℕ) (σ : KFive ≃ₐ[ℚ] KFive) : σ (aCoefficient n) = aCoefficient n := by
  obtain ⟨t, _, hσ⟩ := automorphism_root_power_int σ
  apply Subtype.ext
  change (σ (aCoefficient n) : ℂ) = (aCoefficient n : ℂ)
  rw [← coefficient_galoisA σ t hσ, galoisA_eq_self, aCoefficient_coe]

lemma bCoefficient_fixed (n : ℕ) (σ : KFive ≃ₐ[ℚ] KFive) : σ (bCoefficient n) = bCoefficient n := by
  obtain ⟨t, _, hσ⟩ := automorphism_root_power_int σ
  apply Subtype.ext
  change (σ (bCoefficient n) : ℂ) = (bCoefficient n : ℂ)
  rw [← coefficient_galoisB σ t hσ, galoisB_eq_self, bCoefficient_coe]

/-- All coefficients of the concrete zero-constant generator are rational. -/
theorem A_rational : ∀ n : ℕ, ∃ q : ℚ, (UpperHalfPlane.qExpansion 1 A).coeff n = (q : ℂ) := by
  intro n
  obtain ⟨q, hq⟩ := exists_rational_of_fixed (aCoefficient n) (aCoefficient_fixed n)
  refine ⟨q, ?_⟩
  rw [← coefficient_apply, ← aCoefficient_coe]
  simpa using (congrArg (fun x : KFive => (x : ℂ)) hq).symm

/-- All coefficients of the concrete constant-one generator are rational. -/
theorem B_rational : ∀ n : ℕ, ∃ q : ℚ, (UpperHalfPlane.qExpansion 1 B).coeff n = (q : ℂ) := by
  intro n
  obtain ⟨q, hq⟩ := exists_rational_of_fixed (bCoefficient n) (bCoefficient_fixed n)
  refine ⟨q, ?_⟩
  rw [← coefficient_apply, ← bCoefficient_coe]
  simpa using (congrArg (fun x : KFive => (x : ℂ)) hq).symm

end ZInQ.Contrib.HeckePrimeRationality.NormalizedFive
