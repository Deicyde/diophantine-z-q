/-
Resultant integrality tests and exact contract/body checks.
AI-assisted development; no change to the mathematical declarations.
Checking-add resource limits are not trust levels; closure walks are not library replay.
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
noncomputable section
namespace ResultantIntegralityCases
open Polynomial
namespace AdverseHelpers
def AllR (χ : ℚ[X]) : Prop :=
  ∀ R : ℤ[X], ∃ z : ℤ,
    Polynomial.resultant χ (R.map (Int.castRingHom ℚ)) = (z : ℚ)
def DegreeBoundedAllR (χ : ℚ[X]) : Prop :=
  ∀ R : ℤ[X], R.degree ≤ χ.degree → ∃ z : ℤ,
    Polynomial.resultant χ (R.map (Int.castRingHom ℚ)) = (z : ℚ)
theorem intMap_X :
    (X : ℤ[X]).map (Int.castRingHom ℚ) = (X : ℚ[X]) := by
  simp only [Polynomial.map_X]
theorem intMap_X_add_one :
    (X + 1 : ℤ[X]).map (Int.castRingHom ℚ) = (X + 1 : ℚ[X]) := by
  simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
theorem half_den : (1 / 2 : ℚ).den = 2 := by
  rw [one_div, Rat.den_inv] <;> rfl
theorem third_den : (1 / 3 : ℚ).den = 3 := by
  rw [one_div, Rat.den_inv] <;> rfl
theorem negThird_den : (-(1 / 3 : ℚ)).den = 3 := by
  rw [Rat.neg_den, third_den]
theorem not_intCast_of_den_ne_one (q : ℚ) (hden : q.den ≠ 1) :
    ¬ ∃ z : ℤ, q = (z : ℚ) := by
  rintro ⟨z, hz⟩
  exact hden ((congrArg Rat.den hz).trans (Rat.den_intCast z))
theorem half_not_intCast : ¬ ∃ z : ℤ, (1 / 2 : ℚ) = (z : ℚ) := by
  apply not_intCast_of_den_ne_one (1 / 2 : ℚ)
  rw [half_den] <;> decide
theorem negThird_not_intCast : ¬ ∃ z : ℤ, -(1 / 3 : ℚ) = (z : ℚ) := by
  apply not_intCast_of_den_ne_one (-(1 / 3 : ℚ))
  rw [negThird_den] <;> decide
theorem halfQuadratic_factor :
    (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]) =
      (X + C (1 / 2 : ℚ)) * X := by
  simp only [pow_two, add_mul]
theorem halfQuadratic_monic :
    (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).Monic := by
  rw [halfQuadratic_factor]
  exact (Polynomial.monic_X_add_C (1 / 2 : ℚ)).mul
    (Polynomial.monic_X : (X : ℚ[X]).Monic)
theorem halfQuadratic_natDegree :
    (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).natDegree = 2 := by
  rw [halfQuadratic_factor]
  calc
    ((X + C (1 / 2 : ℚ)) * X : ℚ[X]).natDegree =
        (X + C (1 / 2 : ℚ)).natDegree + (X : ℚ[X]).natDegree :=
      (Polynomial.monic_X_add_C (1 / 2 : ℚ)).natDegree_mul
        (Polynomial.monic_X : (X : ℚ[X]).Monic)
    _ = 2 := by rw [Polynomial.natDegree_X_add_C, Polynomial.natDegree_X]
theorem halfQuadratic_degree :
    (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).degree = 2 := by
  rw [Polynomial.degree_eq_natDegree halfQuadratic_monic.ne_zero,
    halfQuadratic_natDegree]
  decide
theorem int_X_add_one_degree : (X + 1 : ℤ[X]).degree = 1 := by
  simpa only [Polynomial.C_1] using (Polynomial.degree_X_add_C (1 : ℤ))
theorem rat_X_add_one_degree : (X + 1 : ℚ[X]).degree = 1 := by
  simpa only [Polynomial.C_1] using (Polynomial.degree_X_add_C (1 : ℚ))
theorem int_X_add_one_natDegree : (X + 1 : ℤ[X]).natDegree = 1 := by
  simpa only [Polynomial.C_1] using (Polynomial.natDegree_X_add_C (1 : ℤ))
theorem rat_X_add_one_natDegree : (X + 1 : ℚ[X]).natDegree = 1 := by
  simpa only [Polynomial.C_1] using (Polynomial.natDegree_X_add_C (1 : ℚ))
end AdverseHelpers
theorem badHalfLinear_monic : (X - C (1 / 2 : ℚ)).Monic := by
  exact Polynomial.monic_X_sub_C (1 / 2 : ℚ)
theorem badHalfLinear_degree_le :
    (X : ℤ[X]).degree ≤ (X - C (1 / 2 : ℚ)).degree := by
  simpa only [Polynomial.degree_X, Polynomial.degree_X_sub_C] using
    (le_refl (1 : WithBot ℕ))
theorem badHalfLinear_natDegree_le :
    (X : ℤ[X]).natDegree ≤ (X - C (1 / 2 : ℚ)).natDegree := by
  simpa only [Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C] using
    (le_refl (1 : ℕ))
theorem badHalfLinear_mapped_degree_le :
    ((X : ℤ[X]).map (Int.castRingHom ℚ)).degree ≤
      (X - C (1 / 2 : ℚ)).degree := by
  simpa only [AdverseHelpers.intMap_X, Polynomial.degree_X,
    Polynomial.degree_X_sub_C] using (le_refl (1 : WithBot ℕ))
theorem badHalfLinear_resultant :
    Polynomial.resultant (X - C (1 / 2 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (1 / 2 : ℚ) := by
  rw [AdverseHelpers.intMap_X, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X]
  simpa only [Polynomial.eval_X] using
    (Polynomial.resultant_X_sub_C_left (X : ℚ[X]) 1 (1 / 2 : ℚ)
      (by simpa only [Polynomial.natDegree_X] using (le_refl (1 : ℕ))))
theorem badHalfLinear_literal_resultant :
    Polynomial.resultant (X - C (1 / 2 : ℚ)) (X : ℚ[X]) = (1 / 2 : ℚ) := by
  have hmap :
      Polynomial.resultant (X - C (1 / 2 : ℚ))
        ((X : ℤ[X]).map (Int.castRingHom ℚ)) =
      Polynomial.resultant (X - C (1 / 2 : ℚ)) (X : ℚ[X]) :=
    congrArg (fun g : ℚ[X] => Polynomial.resultant (X - C (1 / 2 : ℚ)) g)
      AdverseHelpers.intMap_X
  exact hmap.symm.trans badHalfLinear_resultant
theorem badHalfLinear_negative_sign_false :
    Polynomial.resultant (X - C (1 / 2 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) ≠ -(1 / 2 : ℚ) := by
  rw [badHalfLinear_resultant] <;> norm_num
theorem badHalfLinear_not_intCast :
    ¬ ∃ z : ℤ, Polynomial.resultant (X - C (1 / 2 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ) := by
  rw [badHalfLinear_resultant]
  exact AdverseHelpers.half_not_intCast
theorem badHalfLinear_allR_fails :
    ¬ AdverseHelpers.AllR (X - C (1 / 2 : ℚ)) := by
  intro h
  exact badHalfLinear_not_intCast (h (X : ℤ[X]))
theorem badHalfLinear_degreeBoundedAllR_fails :
    ¬ AdverseHelpers.DegreeBoundedAllR (X - C (1 / 2 : ℚ)) := by
  intro h
  exact badHalfLinear_not_intCast (h (X : ℤ[X]) badHalfLinear_degree_le)
theorem badHalfLinear :
    (X - C (1 / 2 : ℚ)).Monic ∧
    (X : ℤ[X]).degree ≤ (X - C (1 / 2 : ℚ)).degree ∧
    (X : ℤ[X]).natDegree ≤ (X - C (1 / 2 : ℚ)).natDegree ∧
    (X : ℤ[X]).map (Int.castRingHom ℚ) = (X : ℚ[X]) ∧
    ((X : ℤ[X]).map (Int.castRingHom ℚ)).degree ≤
      (X - C (1 / 2 : ℚ)).degree ∧
    Polynomial.resultant (X - C (1 / 2 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (1 / 2 : ℚ) ∧
    (¬ ∃ z : ℤ, Polynomial.resultant (X - C (1 / 2 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
    (¬ AdverseHelpers.AllR (X - C (1 / 2 : ℚ))) ∧
    (¬ AdverseHelpers.DegreeBoundedAllR (X - C (1 / 2 : ℚ))) := by
  exact ⟨badHalfLinear_monic, badHalfLinear_degree_le, badHalfLinear_natDegree_le,
    AdverseHelpers.intMap_X, badHalfLinear_mapped_degree_le,
    badHalfLinear_resultant, badHalfLinear_not_intCast, badHalfLinear_allR_fails,
    badHalfLinear_degreeBoundedAllR_fails⟩
theorem badHalfQuadratic_monic :
    (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).Monic := by
  exact AdverseHelpers.halfQuadratic_monic
theorem badHalfQuadratic_degree_le :
    (X + 1 : ℤ[X]).degree ≤ (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).degree := by
  rw [AdverseHelpers.int_X_add_one_degree, AdverseHelpers.halfQuadratic_degree] <;> decide
theorem badHalfQuadratic_natDegree_le :
    (X + 1 : ℤ[X]).natDegree ≤
      (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).natDegree := by
  rw [AdverseHelpers.int_X_add_one_natDegree, AdverseHelpers.halfQuadratic_natDegree] <;>
    decide
theorem badHalfQuadratic_mapped_degree_le :
    ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)).degree ≤
      (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).degree := by
  rw [AdverseHelpers.intMap_X_add_one, AdverseHelpers.rat_X_add_one_degree,
    AdverseHelpers.halfQuadratic_degree] <;> decide
theorem badHalfQuadratic_resultant :
    Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X)
      ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) = (1 / 2 : ℚ) := by
  rw [AdverseHelpers.intMap_X_add_one, AdverseHelpers.halfQuadratic_natDegree,
    AdverseHelpers.rat_X_add_one_natDegree]
  calc
    Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X) (X + 1) 2 1 =
        (-1 : ℚ) ^ 2 * (X ^ 2 + C (1 / 2 : ℚ) * X).eval (-1) := by
      simpa only [Polynomial.C_1] using
        (Polynomial.resultant_X_add_C_right (X ^ 2 + C (1 / 2 : ℚ) * X) 2 (1 : ℚ)
          (by simpa only [AdverseHelpers.halfQuadratic_natDegree] using
            (le_refl (2 : ℕ))))
    _ = (1 / 2 : ℚ) := by
      norm_num [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
theorem badHalfQuadratic_literal_resultant :
    Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X) (X + 1 : ℚ[X]) =
      (1 / 2 : ℚ) := by
  have hmap :
      Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X)
        ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) =
      Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X) (X + 1 : ℚ[X]) :=
    congrArg (fun g : ℚ[X] => Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X) g)
      AdverseHelpers.intMap_X_add_one
  exact hmap.symm.trans badHalfQuadratic_resultant
theorem badHalfQuadratic_not_intCast :
    ¬ ∃ z : ℤ, Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X)
      ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ) := by
  rw [badHalfQuadratic_resultant]
  exact AdverseHelpers.half_not_intCast
theorem badHalfQuadratic_allR_fails :
    ¬ AdverseHelpers.AllR (X ^ 2 + C (1 / 2 : ℚ) * X) := by
  intro h
  exact badHalfQuadratic_not_intCast (h (X + 1 : ℤ[X]))
theorem badHalfQuadratic_degreeBoundedAllR_fails :
    ¬ AdverseHelpers.DegreeBoundedAllR (X ^ 2 + C (1 / 2 : ℚ) * X) := by
  intro h
  exact badHalfQuadratic_not_intCast (h (X + 1 : ℤ[X]) badHalfQuadratic_degree_le)
theorem badHalfQuadratic_denominator_at_positive_exponent :
    (0 : ℕ) < 1 ∧
    (X ^ 2 + C (1 / 2 : ℚ) * X).coeff 1 = (1 / 2 : ℚ) ∧
    ((X ^ 2 + C (1 / 2 : ℚ) * X).coeff 1).den = 2 ∧
    Nat.Prime ((X ^ 2 + C (1 / 2 : ℚ) * X).coeff 1).den := by
  have hcoeff : (X ^ 2 + C (1 / 2 : ℚ) * X).coeff 1 = (1 / 2 : ℚ) := by
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X]
  have hden : ((X ^ 2 + C (1 / 2 : ℚ) * X).coeff 1).den = 2 := by
    rw [hcoeff, AdverseHelpers.half_den]
  have hprime : Nat.Prime ((X ^ 2 + C (1 / 2 : ℚ) * X).coeff 1).den := by
    rw [hden]
    exact Nat.prime_two
  exact ⟨by decide, hcoeff, hden, hprime⟩
theorem badHalfQuadratic :
    (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).Monic ∧
    (X + 1 : ℤ[X]).degree ≤ (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).degree ∧
    (X + 1 : ℤ[X]).natDegree ≤ (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).natDegree ∧
    (X + 1 : ℤ[X]).map (Int.castRingHom ℚ) = (X + 1 : ℚ[X]) ∧
    ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)).degree ≤
      (X ^ 2 + C (1 / 2 : ℚ) * X : ℚ[X]).degree ∧
    Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X)
      ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) = (1 / 2 : ℚ) ∧
    (¬ ∃ z : ℤ, Polynomial.resultant (X ^ 2 + C (1 / 2 : ℚ) * X)
      ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
    (¬ AdverseHelpers.AllR (X ^ 2 + C (1 / 2 : ℚ) * X)) ∧
    (¬ AdverseHelpers.DegreeBoundedAllR (X ^ 2 + C (1 / 2 : ℚ) * X)) := by
  exact ⟨badHalfQuadratic_monic, badHalfQuadratic_degree_le,
    badHalfQuadratic_natDegree_le, AdverseHelpers.intMap_X_add_one,
    badHalfQuadratic_mapped_degree_le, badHalfQuadratic_resultant,
    badHalfQuadratic_not_intCast, badHalfQuadratic_allR_fails,
    badHalfQuadratic_degreeBoundedAllR_fails⟩
theorem badThirdCubic_monic : (X ^ 3 + C (1 / 3 : ℚ)).Monic := by
  exact Polynomial.monic_X_pow_add_C (n := 3) (1 / 3 : ℚ) (by decide)
theorem badThirdCubic_degree_le :
    (X : ℤ[X]).degree ≤ (X ^ 3 + C (1 / 3 : ℚ)).degree := by
  rw [Polynomial.degree_X,
    Polynomial.degree_X_pow_add_C (n := 3) (by decide) (1 / 3 : ℚ)] <;> decide
theorem badThirdCubic_natDegree_le :
    (X : ℤ[X]).natDegree ≤ (X ^ 3 + C (1 / 3 : ℚ)).natDegree := by
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow_add_C] <;> decide
theorem badThirdCubic_mapped_degree_le :
    ((X : ℤ[X]).map (Int.castRingHom ℚ)).degree ≤
      (X ^ 3 + C (1 / 3 : ℚ)).degree := by
  rw [AdverseHelpers.intMap_X, Polynomial.degree_X,
    Polynomial.degree_X_pow_add_C (n := 3) (by decide) (1 / 3 : ℚ)] <;> decide
theorem badThirdCubic_resultant :
    Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = -(1 / 3 : ℚ) := by
  have hdeg : (X ^ 3 + C (1 / 3 : ℚ)).natDegree = 3 :=
    Polynomial.natDegree_X_pow_add_C
  have heval : (X ^ 3 + C (1 / 3 : ℚ)).eval 0 = (1 / 3 : ℚ) := by
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, zero_pow (by decide : (3 : ℕ) ≠ 0), zero_add]
  have hsign : (-1 : ℚ) ^ 3 = -1 := by norm_num
  have hscalar : (-1 : ℚ) ^ 3 * (X ^ 3 + C (1 / 3 : ℚ)).eval 0 =
      -(1 / 3 : ℚ) := by
    norm_num [hsign, heval]
  have hzeroX : (X - C (0 : ℚ) : ℚ[X]) = X := by
    rw [Polynomial.C_0, sub_zero]
  have htransport :
      Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ)) (X - C (0 : ℚ)) 3 1 =
      Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ)) (X : ℚ[X]) 3 1 :=
    congrArg (fun g : ℚ[X] => Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ)) g 3 1)
      hzeroX
  have hlinear :
      Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ)) (X - C (0 : ℚ)) 3 1 =
      (-1 : ℚ) ^ 3 * (X ^ 3 + C (1 / 3 : ℚ)).eval 0 :=
    Polynomial.resultant_X_sub_C_right (X ^ 3 + C (1 / 3 : ℚ)) 3 (0 : ℚ)
      (by simpa only [hdeg] using (le_refl (3 : ℕ)))
  rw [AdverseHelpers.intMap_X, Polynomial.natDegree_X_pow_add_C,
    Polynomial.natDegree_X]
  exact htransport.symm.trans (hlinear.trans hscalar)
theorem badThirdCubic_literal_resultant :
    Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ)) (X : ℚ[X]) = -(1 / 3 : ℚ) := by
  have hmap :
      Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ))
        ((X : ℤ[X]).map (Int.castRingHom ℚ)) =
      Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ)) (X : ℚ[X]) :=
    congrArg (fun g : ℚ[X] => Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ)) g)
      AdverseHelpers.intMap_X
  exact hmap.symm.trans badThirdCubic_resultant
theorem badThirdCubic_not_intCast :
    ¬ ∃ z : ℤ, Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ) := by
  rw [badThirdCubic_resultant]
  exact AdverseHelpers.negThird_not_intCast
theorem badThirdCubic_allR_fails :
    ¬ AdverseHelpers.AllR (X ^ 3 + C (1 / 3 : ℚ)) := by
  intro h
  exact badThirdCubic_not_intCast (h (X : ℤ[X]))
theorem badThirdCubic_degreeBoundedAllR_fails :
    ¬ AdverseHelpers.DegreeBoundedAllR (X ^ 3 + C (1 / 3 : ℚ)) := by
  intro h
  exact badThirdCubic_not_intCast (h (X : ℤ[X]) badThirdCubic_degree_le)
theorem badThirdCubic_denominator_at_exponent_zero :
    (X ^ 3 + C (1 / 3 : ℚ)).coeff 0 = (1 / 3 : ℚ) ∧
    ((X ^ 3 + C (1 / 3 : ℚ)).coeff 0).den = 3 ∧
    Nat.Prime ((X ^ 3 + C (1 / 3 : ℚ)).coeff 0).den := by
  have hcoeff : (X ^ 3 + C (1 / 3 : ℚ)).coeff 0 = (1 / 3 : ℚ) := by
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  have hden : ((X ^ 3 + C (1 / 3 : ℚ)).coeff 0).den = 3 := by
    rw [hcoeff, AdverseHelpers.third_den]
  have hprime : Nat.Prime ((X ^ 3 + C (1 / 3 : ℚ)).coeff 0).den := by
    rw [hden]
    exact Nat.prime_three
  exact ⟨hcoeff, hden, hprime⟩
theorem badThirdCubic :
    (X ^ 3 + C (1 / 3 : ℚ)).Monic ∧
    (X : ℤ[X]).degree ≤ (X ^ 3 + C (1 / 3 : ℚ)).degree ∧
    (X : ℤ[X]).natDegree ≤ (X ^ 3 + C (1 / 3 : ℚ)).natDegree ∧
    (X : ℤ[X]).map (Int.castRingHom ℚ) = (X : ℚ[X]) ∧
    ((X : ℤ[X]).map (Int.castRingHom ℚ)).degree ≤
      (X ^ 3 + C (1 / 3 : ℚ)).degree ∧
    Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = -(1 / 3 : ℚ) ∧
    (¬ ∃ z : ℤ, Polynomial.resultant (X ^ 3 + C (1 / 3 : ℚ))
      ((X : ℤ[X]).map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
    (¬ AdverseHelpers.AllR (X ^ 3 + C (1 / 3 : ℚ))) ∧
    (¬ AdverseHelpers.DegreeBoundedAllR (X ^ 3 + C (1 / 3 : ℚ))) := by
  exact ⟨badThirdCubic_monic, badThirdCubic_degree_le, badThirdCubic_natDegree_le,
    AdverseHelpers.intMap_X, badThirdCubic_mapped_degree_le,
    badThirdCubic_resultant, badThirdCubic_not_intCast, badThirdCubic_allR_fails,
    badThirdCubic_degreeBoundedAllR_fails⟩
end ResultantIntegralityCases
end
