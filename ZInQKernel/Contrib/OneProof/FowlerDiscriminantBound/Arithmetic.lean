import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! The elementary estimates in Fowler, Proposition 2.7 (pp. 615–616). -/

namespace HDec.CMBranch.FowlerArithmetic

/-- A prime greater than two is at most the square of its predecessor. -/
private theorem prime_le_pred_sq {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p ≤ (p - 1) ^ 2 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  calc
    p ≤ 2 * (p - 1) := by omega
    _ ≤ (p - 1) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right (p - 1) (by omega)

/-- The sharp-for-2 elementary bound `n ≤ 2 φ(n)^2`, including `n = 0`. -/
theorem le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  let S := n.primeFactors
  let T := S.erase 2
  let P := ∏ p ∈ S, p
  let Q := ∏ p ∈ S, (p - 1)
  have hT : (∏ p ∈ T, p) ≤ (∏ p ∈ T, (p - 1)) ^ 2 := by
    rw [pow_two, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro p hp
    rw [← pow_two]
    exact prime_le_pred_sq (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))
      (Finset.ne_of_mem_erase hp)
  have hPQ : P ≤ 2 * Q ^ 2 := by
    by_cases h2 : 2 ∈ S
    · have hP : (∏ p ∈ T, p) * 2 = P := Finset.prod_erase_mul S id h2
      have hQ0 := Finset.prod_erase_mul S (fun p : ℕ => p - 1) h2
      have hQ : (∏ p ∈ T, (p - 1)) = Q := by simpa [T, Q] using hQ0
      rw [← hP, ← hQ, mul_comm _ 2]
      exact Nat.mul_le_mul_left 2 hT
    · have h := Finset.erase_eq_of_notMem h2
      simp only [T, h] at hT
      change P ≤ Q ^ 2 at hT
      exact hT.trans (by omega)
  let d := n / P
  have hd : d * P = n := Nat.div_mul_cancel (Nat.prod_primeFactors_dvd n)
  have hφ : n.totient = d * Q := Nat.totient_eq_div_primeFactors_mul n
  have hdpos : 1 ≤ d := by
    by_contra! h
    have hzero : d = 0 := Nat.lt_one_iff.mp h
    have hzn : 0 = n := by simpa only [hzero, zero_mul] using hd
    exact hn hzn.symm
  calc
    n = d * P := hd.symm
    _ ≤ d * (2 * Q ^ 2) := Nat.mul_le_mul_left d hPQ
    _ ≤ d ^ 2 * (2 * Q ^ 2) := Nat.mul_le_mul_right _ (by nlinarith)
    _ = 2 * n.totient ^ 2 := by rw [hφ]; ring

private theorem sqrt_abs_factor (D : ℤ) (f : ℕ) :
    Real.sqrt |((((f : ℤ) ^ 2 * D : ℤ) : ℝ))| = (f : ℝ) * Real.sqrt |(D : ℝ)| := by
  push_cast
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ f)]

/-- Ordinary unit-index case, using the logarithmic field-discriminant estimate. -/
theorem bound_of_log {D : ℤ} (hD : D < 0) {n f : ℕ}
    (hf : f ≤ 2 * n ^ 2) (hlog : Real.log |(D : ℝ)| ≤ 42000 * (n : ℝ) ^ 2) :
    Real.sqrt |((((f : ℤ) ^ 2 * D : ℤ) : ℝ))| ≤
      2 * (n : ℝ) ^ 2 * Real.exp (21000 * (n : ℝ) ^ 2) := by
  have hDz : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne
  have hExp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (abs_pos.mpr hDz), show (42000 : ℝ) * (n : ℝ) ^ 2 =
    21000 * (n : ℝ) ^ 2 + 21000 * (n : ℝ) ^ 2 by ring, Real.exp_add, ← pow_two] at hExp
  have hR := (Real.sqrt_le_iff.mpr ⟨Real.exp_nonneg _, hExp⟩)
  rw [sqrt_abs_factor]
  exact mul_le_mul (by exact_mod_cast hf) hR (Real.sqrt_nonneg _) (by positivity)

/-- Exceptional unit-index case `D = -3` or `D = -4`. -/
theorem bound_of_small {D : ℤ} (hD : D = -3 ∨ D = -4) {n f : ℕ} (hn : 0 < n)
    (hf : f ≤ 18 * n ^ 2) : Real.sqrt |((((f : ℤ) ^ 2 * D : ℤ) : ℝ))| ≤
      2 * (n : ℝ) ^ 2 * Real.exp (21000 * (n : ℝ) ^ 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : Real.sqrt |(D : ℝ)| ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    rcases hD with rfl | rfl <;> norm_num
  have he : (18 : ℝ) ≤ Real.exp (21000 * (n : ℝ) ^ 2) := by
    calc
      18 ≤ 21000 * (n : ℝ) ^ 2 + 1 := by nlinarith
      _ ≤ _ := Real.add_one_le_exp _
  rw [sqrt_abs_factor]
  calc
    (f : ℝ) * Real.sqrt |(D : ℝ)| ≤ (18 * (n : ℝ) ^ 2) * 2 :=
      mul_le_mul (by exact_mod_cast hf) hR (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * (n : ℝ) ^ 2 * 18 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

end HDec.CMBranch.FowlerArithmetic
