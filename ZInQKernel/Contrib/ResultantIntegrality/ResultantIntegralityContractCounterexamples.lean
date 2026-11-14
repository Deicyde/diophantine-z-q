/-
Resultant integrality tests and exact contract/body checks.
AI-assisted development; no change to the mathematical declarations.
Checking-add resource limits are not trust levels; closure walks are not library replay.
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
noncomputable section
open Polynomial
namespace ResultantIntegralityContractCases
def monicLinearChi : Polynomial ℚ := X - C (1 / 2 : ℚ)
def nonmonicConstantChi : Polynomial ℚ := C (1 / 2 : ℚ)
theorem intCast_ne_half (z : ℤ) : (z : ℚ) ≠ (1 / 2 : ℚ) := by
  intro h
  have hq : (2 : ℚ) * (z : ℚ) = 1 := by
    rw [h]
    norm_num
  have hi : (2 : ℤ) * z = 1 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hq
  omega
theorem mapped_integer_polynomial_eq_C (R : Polynomial ℤ)
    (hR : R.natDegree = 0) :
    R.map (Int.castRingHom ℚ) = C (R.coeff 0 : ℚ) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (Polynomial.eq_C_of_natDegree_eq_zero hR)
  simpa only [Polynomial.map_C, Int.coe_castRingHom] using h
theorem monicLinearChi_natDegree : monicLinearChi.natDegree = 1 := by
  simpa only [monicLinearChi] using
    Polynomial.natDegree_X_sub_C (1 / 2 : ℚ)
theorem monicLinearChi_degree :
    monicLinearChi.degree = (1 : WithBot ℕ) := by
  simpa only [monicLinearChi] using
    Polynomial.degree_X_sub_C (1 / 2 : ℚ)
theorem monicLinearChi_monic : monicLinearChi.Monic := by
  simpa only [monicLinearChi] using
    Polynomial.monic_X_sub_C (1 / 2 : ℚ)
theorem monicLinearChi_coeff_zero :
    monicLinearChi.coeff 0 = -(1 / 2 : ℚ) := by
  simp only [monicLinearChi, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
    Polynomial.coeff_C_zero, zero_sub]
theorem monicLinearChi_resultant_lt_eq (R : Polynomial ℤ)
    (hR : R.natDegree < monicLinearChi.natDegree) :
    monicLinearChi.resultant (R.map (Int.castRingHom ℚ)) = (R.coeff 0 : ℚ) := by
  have hR0 : R.natDegree = 0 := by
    rw [monicLinearChi_natDegree] at hR
    omega
  have hmap := mapped_integer_polynomial_eq_C R hR0
  simp only [hmap, monicLinearChi_natDegree, Polynomial.natDegree_C,
    Polynomial.resultant_C_right, pow_zero, pow_one, one_mul]
  have htransport :
      monicLinearChi.resultant (R.map (Int.castRingHom ℚ)) 1 0 =
      monicLinearChi.resultant (C (R.coeff 0 : ℚ)) 1 0 :=
    congrArg (fun g : ℚ[X] => monicLinearChi.resultant g 1 0) hmap
  have hconstant : monicLinearChi.resultant (C (R.coeff 0 : ℚ)) 1 0 =
      (R.coeff 0 : ℚ) :=
    (Polynomial.resultant_C_zero_right (f := monicLinearChi) (m := 1)
      (R.coeff 0 : ℚ)).trans (pow_one (R.coeff 0 : ℚ))
  exact htransport.trans hconstant
theorem monicLinearChi_integer_resultants_lt :
    ∀ R : Polynomial ℤ, R.natDegree < monicLinearChi.natDegree →
      ∃ z : ℤ, monicLinearChi.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ) := by
  intro R hR
  exact ⟨R.coeff 0, monicLinearChi_resultant_lt_eq R hR⟩
theorem monicLinearChi_resultants_lt_mem_intRange :
    ∀ R : Polynomial ℤ, R.natDegree < monicLinearChi.natDegree →
      monicLinearChi.resultant (R.map (Int.castRingHom ℚ)) ∈
        Set.range (Int.castRingHom ℚ) := by
  intro R hR
  refine ⟨R.coeff 0, ?_⟩
  change (R.coeff 0 : ℚ) = monicLinearChi.resultant (R.map (Int.castRingHom ℚ))
  exact (monicLinearChi_resultant_lt_eq R hR).symm
theorem monicLinearChi_no_integer_lift :
    ¬ ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = monicLinearChi := by
  rintro ⟨P, hP⟩
  have h0 : (P.coeff 0 : ℚ) = -(1 / 2 : ℚ) := by
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom, monicLinearChi_coeff_zero]
      using congrArg (fun p : Polynomial ℚ => p.coeff 0) hP
  have hneg : ((-(P.coeff 0) : ℤ) : ℚ) = (1 / 2 : ℚ) := by
    rw [Int.cast_neg, h0, neg_neg]
  exact intCast_ne_half (-(P.coeff 0)) hneg
theorem monicLinearChi_not_mem_lifts :
    monicLinearChi ∉ Polynomial.lifts (Int.castRingHom ℚ) := by
  intro h
  exact monicLinearChi_no_integer_lift
    ((Polynomial.mem_lifts (f := Int.castRingHom ℚ) monicLinearChi).mp h)
theorem monicLinearChi_X_test_degree :
    (X : Polynomial ℤ).natDegree = monicLinearChi.natDegree := by
  simp only [Polynomial.natDegree_X, monicLinearChi_natDegree]
theorem monicLinearChi_resultant_X :
    monicLinearChi.resultant ((X : Polynomial ℤ).map (Int.castRingHom ℚ)) =
      (1 / 2 : ℚ) := by
  have hX : ((X : Polynomial ℤ).map (Int.castRingHom ℚ)) = (X : ℚ[X]) :=
    Polynomial.map_X (Int.castRingHom ℚ)
  have htransport :
      monicLinearChi.resultant ((X : Polynomial ℤ).map (Int.castRingHom ℚ)) =
      monicLinearChi.resultant (X : ℚ[X]) :=
    congrArg (fun g : ℚ[X] => monicLinearChi.resultant g) hX
  have hliteral : monicLinearChi.resultant (X : ℚ[X]) = (1 / 2 : ℚ) := by
    rw [monicLinearChi_natDegree, Polynomial.natDegree_X]
    change Polynomial.resultant (X - C (1 / 2 : ℚ)) (X : ℚ[X]) 1 1 = (1 / 2 : ℚ)
    simpa only [Polynomial.eval_X] using
      (Polynomial.resultant_X_sub_C_left (g := (X : ℚ[X])) (n := 1) (1 / 2 : ℚ)
        (by simpa only [Polynomial.natDegree_X] using (le_refl (1 : ℕ))))
  exact htransport.trans hliteral
theorem monicLinearChi_genuine_le_input_fails :
    ¬ (∀ R : Polynomial ℤ, R.natDegree ≤ monicLinearChi.natDegree →
      ∃ z : ℤ, monicLinearChi.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) := by
  intro h
  have hX : (X : Polynomial ℤ).natDegree ≤ monicLinearChi.natDegree := by
    simpa only [Polynomial.natDegree_X, monicLinearChi_natDegree] using
      (le_refl (1 : ℕ))
  obtain ⟨z, hz⟩ := h (X : Polynomial ℤ) hX
  exact intCast_ne_half z (hz.symm.trans monicLinearChi_resultant_X)
theorem strict_degree_counterexample :
    monicLinearChi.Monic ∧ monicLinearChi.natDegree = 1 ∧
      (∀ R : Polynomial ℤ, R.natDegree < monicLinearChi.natDegree →
        ∃ z : ℤ, monicLinearChi.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
      (¬ ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = monicLinearChi) := by
  exact ⟨monicLinearChi_monic, monicLinearChi_natDegree,
    monicLinearChi_integer_resultants_lt, monicLinearChi_no_integer_lift⟩
theorem nonmonicConstantChi_natDegree : nonmonicConstantChi.natDegree = 0 := by
  simp only [nonmonicConstantChi, Polynomial.natDegree_C]
theorem nonmonicConstantChi_degree :
    nonmonicConstantChi.degree = (0 : WithBot ℕ) := by
  simpa only [nonmonicConstantChi] using
    (Polynomial.degree_C (by norm_num : (1 / 2 : ℚ) ≠ 0))
theorem nonmonicConstantChi_leadingCoeff :
    nonmonicConstantChi.leadingCoeff = (1 / 2 : ℚ) := by
  simp only [nonmonicConstantChi, Polynomial.leadingCoeff_C]
theorem nonmonicConstantChi_not_monic : ¬ nonmonicConstantChi.Monic := by
  intro h
  have hh : (1 / 2 : ℚ) = 1 := by
    simpa only [nonmonicConstantChi_leadingCoeff] using h.leadingCoeff
  norm_num at hh
theorem nonmonicConstantChi_resultant_le_eq_one (R : Polynomial ℤ)
    (hR : R.natDegree ≤ nonmonicConstantChi.natDegree) :
    nonmonicConstantChi.resultant (R.map (Int.castRingHom ℚ)) = 1 := by
  have hR0 : R.natDegree = 0 := by
    rw [nonmonicConstantChi_natDegree] at hR
    omega
  have hmap := mapped_integer_polynomial_eq_C R hR0
  simp only [hmap, nonmonicConstantChi_natDegree, Polynomial.natDegree_C,
    Polynomial.resultant_C_right, pow_zero, mul_one]
  have htransport :
      nonmonicConstantChi.resultant (R.map (Int.castRingHom ℚ)) 0 0 =
      nonmonicConstantChi.resultant (C (R.coeff 0 : ℚ)) 0 0 :=
    congrArg (fun g : ℚ[X] => nonmonicConstantChi.resultant g 0 0) hmap
  have hconstant : nonmonicConstantChi.resultant (C (R.coeff 0 : ℚ)) 0 0 = 1 :=
    (Polynomial.resultant_C_zero_right (f := nonmonicConstantChi) (m := 0)
      (R.coeff 0 : ℚ)).trans (pow_zero (R.coeff 0 : ℚ))
  exact htransport.trans hconstant
theorem nonmonicConstantChi_integer_resultants_le :
    ∀ R : Polynomial ℤ, R.natDegree ≤ nonmonicConstantChi.natDegree →
      ∃ z : ℤ, nonmonicConstantChi.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ) := by
  intro R hR
  refine ⟨1, ?_⟩
  simpa only [Int.cast_one] using nonmonicConstantChi_resultant_le_eq_one R hR
theorem nonmonicConstantChi_resultants_le_mem_intRange :
    ∀ R : Polynomial ℤ, R.natDegree ≤ nonmonicConstantChi.natDegree →
      nonmonicConstantChi.resultant (R.map (Int.castRingHom ℚ)) ∈
        Set.range (Int.castRingHom ℚ) := by
  intro R hR
  refine ⟨(1 : ℤ), ?_⟩
  change (1 : ℚ) = nonmonicConstantChi.resultant (R.map (Int.castRingHom ℚ))
  exact (nonmonicConstantChi_resultant_le_eq_one R hR).symm
theorem nonmonicConstantChi_zero_test_nominal_zero_zero :
    nonmonicConstantChi.resultant ((0 : Polynomial ℤ).map (Int.castRingHom ℚ)) =
      Polynomial.resultant nonmonicConstantChi (0 : Polynomial ℚ) 0 0 := by
  simp only [Polynomial.map_zero, nonmonicConstantChi_natDegree, Polynomial.natDegree_zero]
  exact congrArg (fun g : ℚ[X] => Polynomial.resultant nonmonicConstantChi g 0 0)
    (Polynomial.map_zero (Int.castRingHom ℚ))
theorem nonmonicConstantChi_nominal_zero_zero_eq_one :
    Polynomial.resultant nonmonicConstantChi (0 : Polynomial ℚ) 0 0 = 1 := by
  simp only [Polynomial.resultant_zero_right_deg, pow_zero]
theorem nonmonicConstantChi_resultant_zero :
    nonmonicConstantChi.resultant ((0 : Polynomial ℤ).map (Int.castRingHom ℚ)) = 1 := by
  exact nonmonicConstantChi_zero_test_nominal_zero_zero.trans
    nonmonicConstantChi_nominal_zero_zero_eq_one
theorem nonmonicConstantChi_no_integer_lift :
    ¬ ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = nonmonicConstantChi := by
  rintro ⟨P, hP⟩
  have h0 : (P.coeff 0 : ℚ) = (1 / 2 : ℚ) := by
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom, nonmonicConstantChi,
      Polynomial.coeff_C_zero] using congrArg (fun p : Polynomial ℚ => p.coeff 0) hP
  exact intCast_ne_half (P.coeff 0) h0
theorem nonmonicConstantChi_not_mem_lifts :
    nonmonicConstantChi ∉ Polynomial.lifts (Int.castRingHom ℚ) := by
  intro h
  exact nonmonicConstantChi_no_integer_lift
    ((Polynomial.mem_lifts (f := Int.castRingHom ℚ) nonmonicConstantChi).mp h)
theorem dropping_monicity_counterexample :
    nonmonicConstantChi.natDegree = 0 ∧ (¬ nonmonicConstantChi.Monic) ∧
      (∀ R : Polynomial ℤ, R.natDegree ≤ nonmonicConstantChi.natDegree →
        ∃ z : ℤ, nonmonicConstantChi.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) ∧
      (¬ ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) = nonmonicConstantChi) := by
  exact ⟨nonmonicConstantChi_natDegree, nonmonicConstantChi_not_monic,
    nonmonicConstantChi_integer_resultants_le, nonmonicConstantChi_no_integer_lift⟩
end ResultantIntegralityContractCases
