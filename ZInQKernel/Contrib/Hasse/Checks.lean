import ZInQKernel.Contrib.Hasse.Convergence

/-! Exact statement and edge-case checks for the P4 contribution.
This is contributor validation, not protected independent Astra acceptance. -/

open scoped LSeries.notation
open ZInQ.Contrib.Hasse ZInQ.Literature ZInQ WeierstrassCurve PowerSeries

-- Generic arithmetic scope: no Hasse input, implicit typeclass assumption, or fixed d.
example (d p : ℕ) [Fact p.Prime] (hd : Odd d) (hsq : Squarefree d)
    (hpd : ¬ p ∣ 2 * d) :
    |(((shortCurve (-(d : ℚ) ^ 2)).LFunction p : ℤ) : ℝ)| ≤ 2 * Real.sqrt p :=
  LFunction_cd_prime_hasse hd hsq p hpd

example (d : ℕ) (hd : Odd d) (hsq : Squarefree d) (s : ℂ)
    (hs : (3 / 2 : ℝ) < s.re) :
    LSeriesSummable (fun n => (((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℤ) : ℂ)) s :=
  LFunction_cd_summable hd hsq hs

-- Hasse endpoint / repeated roots and the degenerate p = 0 generic root lemma.
example : ∃ α β : ℂ, α + β = 2 ∧ α * β = 1 ∧ ‖α‖ = 1 ∧ ‖β‖ = 1 := by
  convert exists_hasse_roots (a := 2) (p := 1) (by norm_num) (by norm_num) using 1 <;> norm_num

example : ∃ α β : ℂ, α + β = 0 ∧ α * β = 0 ∧ ‖α‖ = 0 ∧ ‖β‖ = 0 := by
  convert exists_hasse_roots (a := 0) (p := 0) (by norm_num) (by norm_num) using 1 <;> norm_num

-- k = 0, bad-prime inverse, and n = 0 belong to the proved interfaces.
example (d p : ℕ) [Fact p.Prime] (hd : Odd d) (hsq : Squarefree d) :
    ‖((coeff 0 (invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) : ℤ) : ℂ)‖ ≤ 1 := by
  convert norm_cdEuler_coeff_le hd hsq p 0 using 1 <;> norm_num

example : (sqrtSeq ⍟ sqrtSeq) 0 = 0 := by
  rw [sqrtSeq_convolution]; simp

#print axioms eta
#print axioms quadratic_unique
#print axioms exists_quartic
#print axioms norm_jacobiSum
#print axioms eta_inv
#print axioms sum_comp_sq
#print axioms cubic_sum_eq_jacobi
#print axioms cubic_sum_twist
#print axioms norm_cubic_sum_le
#print axioms affine_count_eq_char_sum
#print axioms sum_eta_of_odd
#print axioms norm_cubic_sum_le_all
#print axioms abs_affine_trace_le
#print axioms LFunction_cd_prime_hasse
#print axioms exists_hasse_roots
#print axioms geometric_mul
#print axioms coeff_inv_euler_eq
#print axioms coeff_inv_euler_recurrence
#print axioms norm_coeff_inv_euler_le
#print axioms norm_cdEuler_coeff_le
#print axioms sqrt_pow
#print axioms norm_LFunction_cd_le
#print axioms sqrtSeq
#print axioms sqrtSeq_convolution
#print axioms sqrtSeq_summable
#print axioms LFunction_cd_summable
