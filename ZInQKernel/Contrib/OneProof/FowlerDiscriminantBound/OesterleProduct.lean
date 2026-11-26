import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.Reduction
import Mathlib.Data.Nat.Sqrt

/-! The explicit local-product estimate in Oesterlé, Exp. 631, Theorem 1 and §5.1. -/

namespace HDec.CMBranch.FowlerArithmetic

/-- `Nat.sqrt (4*p)` is the integer part of `2√p`, as in Oesterlé's local factor. -/
noncomputable def oesterleFactor (p : ℕ) : ℝ := 1 - (Nat.sqrt (4 * p) : ℝ) / ((p : ℝ) + 1)

private noncomputable def scaledFactor (p : ℕ) : ℝ := 2 * oesterleFactor p

private def smallPrimes : Finset ℕ := {2, 3, 5, 7}

private theorem scaledFactor_two : scaledFactor 2 = 2/3 := by
  norm_num [scaledFactor, oesterleFactor,
    show Nat.sqrt (4 * 2) = 2 by symm; exact Nat.eq_sqrt'.mpr (by norm_num)]

private theorem scaledFactor_three : scaledFactor 3 = 1/2 := by
  norm_num [scaledFactor, oesterleFactor,
    show Nat.sqrt (4 * 3) = 3 by symm; exact Nat.eq_sqrt'.mpr (by norm_num)]

private theorem scaledFactor_five : scaledFactor 5 = 2/3 := by
  norm_num [scaledFactor, oesterleFactor,
    show Nat.sqrt (4 * 5) = 4 by symm; exact Nat.eq_sqrt'.mpr (by norm_num)]

private theorem scaledFactor_seven : scaledFactor 7 = 3/4 := by
  norm_num [scaledFactor, oesterleFactor,
    show Nat.sqrt (4 * 7) = 5 by symm; exact Nat.eq_sqrt'.mpr (by norm_num)]

private theorem scaledFactor_small {p : ℕ} (hp : p ∈ smallPrimes) :
    0 ≤ scaledFactor p ∧ scaledFactor p ≤ 1 := by
  simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    norm_num [scaledFactor_two, scaledFactor_three, scaledFactor_five, scaledFactor_seven]

private theorem one_le_scaledFactor {p : ℕ} (hp : p.Prime) (hsmall : p ∉ smallPrimes) :
    1 ≤ scaledFactor p := by
  by_cases h14 : 14 ≤ p
  · have hpR : (14 : ℝ) ≤ p := by exact_mod_cast h14
    have hs : ((Nat.sqrt (4 * p) : ℕ) : ℝ)^2 ≤ 4 * (p : ℝ) := by
      exact_mod_cast Nat.sqrt_le' (4*p)
    have hsq : (2 * (Nat.sqrt (4 * p) : ℝ))^2 ≤ ((p : ℝ) + 1)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpR) (Nat.cast_nonneg (α := ℝ) p)]
    have hd : 2 * (Nat.sqrt (4 * p) : ℝ) ≤ (p : ℝ) + 1 := by
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    have hq : (Nat.sqrt (4 * p) : ℝ) / ((p : ℝ) + 1) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith
    unfold scaledFactor oesterleFactor
    linarith
  · have h2 := hp.two_le
    have h13 : p ≤ 13 := by omega
    have s11 : Nat.sqrt (4 * 11) = 6 := by symm; exact Nat.eq_sqrt'.mpr (by norm_num)
    have s13 : Nat.sqrt (4 * 13) = 7 := by symm; exact Nat.eq_sqrt'.mpr (by norm_num)
    interval_cases p <;> norm_num [smallPrimes, scaledFactor, oesterleFactor, s11, s13] at *

private theorem prod_scaledFactor_small : ∏ p ∈ smallPrimes, scaledFactor p = 1/6 := by
  norm_num [smallPrimes, Finset.prod_insert, scaledFactor_two, scaledFactor_three,
    scaledFactor_five, scaledFactor_seven]

/-- Explicit product estimate for any subset of prime divisors, including the empty set. -/
theorem oesterle_product_estimate (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (1 : ℝ)/6 ≤ (2 : ℝ)^S.card * ∏ p ∈ S, oesterleFactor p := by
  have hlow : (1 : ℝ)/6 ≤ ∏ p ∈ S ∩ smallPrimes, scaledFactor p := by
    rw [← prod_scaledFactor_small]
    apply Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right
    · exact fun p hp => (scaledFactor_small hp).1
    · exact fun p hp _ => (scaledFactor_small hp).2
  have hhigh : 1 ≤ ∏ p ∈ S \ smallPrimes, scaledFactor p := by
    apply Finset.one_le_prod₀
    intro p hp
    obtain ⟨hpS, hps⟩ := Finset.mem_sdiff.mp hp
    exact one_le_scaledFactor (hS p hpS) hps
  have hsplit : (∏ p ∈ S \ smallPrimes, scaledFactor p) *
      (∏ p ∈ S ∩ smallPrimes, scaledFactor p) = ∏ p ∈ S, scaledFactor p := by
    rw [show S \ smallPrimes = S \ (S ∩ smallPrimes) by ext p; simp]
    exact Finset.prod_sdiff Finset.inter_subset_left
  have htot : (1 : ℝ)/6 ≤ ∏ p ∈ S, scaledFactor p := by
    rw [← hsplit]
    simpa only [one_mul] using mul_le_mul hhigh hlow (by norm_num) (by linarith)
  simpa [scaledFactor, Finset.prod_mul_distrib] using htot

end HDec.CMBranch.FowlerArithmetic
