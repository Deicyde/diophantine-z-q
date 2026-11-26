import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.Oesterle
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Picard
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# The Fowler bound on the actual order and its maximal order

The analytic estimate and genus divisibility are used at the field discriminant, with
`NumberField.classNumber K`. The conductor product of Cox, Theorem 7.24, uses the same
field and the Picard group of the given order. The field and order are not selected
independently. For a quadratic order the conductor is its index times the maximal order.
-/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The cardinality of the maximal order's Picard group is the field class number. -/
theorem card_pic_maximal : Nat.card (Pic (maximalNumberFieldOrder K)) = classNumber K := by
  change Nat.card (ClassGroup (𝓞 K)) = classNumber K
  rw [classNumber, Nat.card_eq_fintype_card]

/-- The conductor-product lower bound with the same field and the same given order.
The unit index is `u`; `s` is the Kronecker symbol of the field discriminant. -/
theorem classNumber_mul_totient_le_pic_mul {O : NumberFieldOrder K} {u : ℕ} {s : ℕ → ℤ}
    (hs : ∀ p ∈ O.index.primeFactors, s p ≤ 1)
    (hcox : (Nat.card (Pic O) : ℝ) * (u : ℝ) =
      (classNumber K : ℝ) * (O.index : ℝ) *
        ∏ p ∈ O.index.primeFactors, (1 - (s p : ℝ) / (p : ℝ))) :
    classNumber K * O.index.totient ≤ Nat.card (Pic O) * u := by
  have hφ : (O.index.totient : ℝ) =
      (O.index : ℝ) * ∏ p ∈ O.index.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors O.index)
    push_cast at h
    exact h
  have hprod : (O.index.totient : ℝ) ≤
      (O.index : ℝ) * ∏ p ∈ O.index.primeFactors, (1 - (s p : ℝ) / (p : ℝ)) := by
    rw [hφ]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp' : (1 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')
    · intro p hp
      have h : (s p : ℝ) ≤ 1 := by exact_mod_cast hs p hp
      rw [← one_div]
      exact sub_le_sub_left (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)) _
  have h := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg (classNumber K))
  rw [← mul_assoc, ← hcox] at h
  exact_mod_cast h

/-- The bound for an actual order. The hypotheses are the logarithmic estimate on the
same field and the part of the Cox conductor formula used by Fowler, Proposition 2.7. -/
theorem fowler_bound_of_pic {O : NumberFieldOrder K} {n u : ℕ}
    (hD : NumberField.discr K < 0)
    (hlog : Real.log |(NumberField.discr K : ℝ)| ≤ 42000 * (classNumber K : ℝ)^2)
    (hu : u ≤ 3) (hu1 : NumberField.discr K ≠ -3 → NumberField.discr K ≠ -4 → u = 1)
    (hcox : classNumber K * O.index.totient ≤ Nat.card (Pic O) * u)
    (hn : 0 < n) (hh : Nat.card (Pic O) ≤ n) :
    Real.sqrt |(O.discr : ℝ)| ≤ 2 * (n : ℝ)^2 * Real.exp (21000 * (n : ℝ)^2) := by
  rw [O.discr_eq_index_sq_mul]
  have hc : 1 ≤ classNumber K := classNumber_pos K
  have hf : 0 < O.index := Nat.pos_of_ne_zero O.index_ne_zero
  have hφ : 1 ≤ O.index.totient := Nat.totient_pos.mpr hf
  have hφc : O.index.totient ≤ classNumber K * O.index.totient := by
    simpa only [one_mul] using Nat.mul_le_mul_right O.index.totient hc
  by_cases hsmall : NumberField.discr K = -3 ∨ NumberField.discr K = -4
  · have hφn : O.index.totient ≤ 3 * n :=
      hφc.trans (hcox.trans (by simpa [Nat.mul_comm 3] using Nat.mul_le_mul hh hu))
    apply bound_of_small hsmall hn
    calc
      O.index ≤ 2 * O.index.totient^2 := le_two_mul_totient_sq _
      _ ≤ 2 * (3 * n)^2 := by gcongr
      _ = 18 * n^2 := by ring
  · push Not at hsmall
    rw [hu1 hsmall.1 hsmall.2, mul_one] at hcox
    have hcn : classNumber K ≤ n := by
      have h := Nat.mul_le_mul_left (classNumber K) hφ
      rw [mul_one] at h
      exact h.trans (hcox.trans hh)
    have hφn : O.index.totient ≤ n := hφc.trans (hcox.trans hh)
    apply bound_of_log hD ((le_two_mul_totient_sq _).trans (by gcongr))
    exact hlog.trans (by gcongr)

end HDec.CMBranch.FowlerArithmetic
