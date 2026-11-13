import ZInQKernel.Contrib.Hasse.PointCount
import ZInQKernel.Contrib.Hasse.EulerBounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Absolute convergence in `Re(s) > 3/2`

The majorant is `τ(n) √n`, obtained from the formal Euler coefficients. Its
L-series is the Dirichlet convolution of two copies of the sequence `√n`.
Thus no unformalized divisor-function asymptotic estimate is needed.
-/

namespace ZInQ.Contrib.Hasse

open ZInQ.Literature WeierstrassCurve PowerSeries
open scoped LSeries.notation

/-- Every formal local coefficient has the Hasse root majorant; bad primes
have inverse Euler factor `1` and are included explicitly, also at `k = 0`. -/
theorem norm_cdEuler_coeff_le {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ‖((coeff k (invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) : ℤ) : ℂ)‖ ≤
      (k + 1) * (Real.sqrt p) ^ k := by
  by_cases hpd : p ∣ 2 * d
  · have hP : cdEulerPoly d p = 1 := by simp [cdEulerPoly, hpd]
    have hS : invOfUnit (1 : PowerSeries ℤ) 1 = 1 := by
      simpa using mul_invOfUnit (1 : PowerSeries ℤ) 1 (by simp)
    rw [hP, Polynomial.coe_one, hS]
    by_cases hk : k = 0
    · subst hk; simp
    · simp only [coeff_one, hk, ↓reduceIte, Int.cast_zero, norm_zero]
      positivity
  · have ha := LFunction_cd_prime_hasse hd hsq p hpd
    rw [LFunction_cd_apply_prime hd hsq p] at ha
    simp only [hpd, ↓reduceIte] at ha
    simpa only [cdEulerPoly, hpd, ↓reduceIte, cdModel_eq_shortCurve,
      Int.cast_natCast] using
      norm_coeff_inv_euler_le
        ((p : ℤ) + 1 - Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point)
        (p : ℤ) (by positivity) ha k

/-- Square roots commute with natural powers on nonnegative reals. -/
theorem sqrt_pow (p : ℝ) (hp : 0 ≤ p) (k : ℕ) :
    Real.sqrt (p ^ k) = (Real.sqrt p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hp k), ih, pow_succ]

/-- The global formal coefficient is dominated by the divisor-count majorant. -/
theorem norm_LFunction_cd_le {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (n : ℕ) :
    ‖(((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℤ) : ℂ)‖ ≤
      (n.divisors.card : ℝ) * Real.sqrt n := by
  by_cases hn : n = 0
  · subst hn; simp
  rw [LFunction_cd_apply hd hsq hn, Finsupp.prod, Int.cast_prod, norm_prod]
  have hlocal (p : ℕ) (hp : p ∈ n.factorization.support) :
      ‖((coeff (n.factorization p) (invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) : ℤ) : ℂ)‖ ≤
        (n.factorization p + 1) * (Real.sqrt p) ^ n.factorization p := by
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)⟩
    exact norm_cdEuler_coeff_le hd hsq p _
  calc
    _ ≤ ∏ p ∈ n.factorization.support,
        ((n.factorization p + 1) : ℝ) * (Real.sqrt p) ^ n.factorization p := by
      gcongr with p hp
      exact hlocal p hp
    _ = (∏ p ∈ n.factorization.support, ((n.factorization p + 1) : ℝ)) *
        (∏ p ∈ n.factorization.support, (Real.sqrt p) ^ n.factorization p) := Finset.prod_mul_distrib
    _ = (n.divisors.card : ℝ) * Real.sqrt n := by
      congr 1
      · have hc : n.divisors.card = ∏ p ∈ n.factorization.support, (n.factorization p + 1) := by
          rw [Nat.support_factorization]; exact Nat.card_divisors hn
        rw [hc]
        simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_one]
      · have ht (p : ℕ) : (Real.sqrt (p : ℝ)) ^ n.factorization p =
            Real.sqrt ((p : ℝ) ^ n.factorization p) :=
          (sqrt_pow _ (Nat.cast_nonneg _) _).symm
        simp_rw [ht]
        rw [← Real.sqrt_prod _ (fun _ _ => by positivity)]
        have hp : (∏ p ∈ n.factorization.support, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
          exact_mod_cast Nat.prod_factorization_pow_eq_self hn
        rw [hp]

/-- The square-root sequence used in the convolution majorant. -/
noncomputable def sqrtSeq (n : ℕ) : ℂ := (Real.sqrt n : ℂ)

/-- Exact identity of the analytic majorant with the divisor count. -/
theorem sqrtSeq_convolution (n : ℕ) :
    (sqrtSeq ⍟ sqrtSeq) n = ((n.divisors.card : ℝ) * Real.sqrt n : ℂ) := by
  rw [LSeries.convolution_def]
  dsimp only
  rw [Nat.sum_divisorsAntidiagonal (fun i j => sqrtSeq i * sqrtSeq j)]
  have hterm (i : ℕ) (hi : i ∈ n.divisors) : sqrtSeq i * sqrtSeq (n / i) = sqrtSeq n := by
    dsimp [sqrtSeq]
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity), ← Nat.cast_mul,
      Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hi)]
  rw [Finset.sum_congr rfl hterm]
  simp [sqrtSeq, nsmul_eq_mul]

/-- Each square-root Dirichlet series converges absolutely in the desired half-plane. -/
theorem sqrtSeq_summable {s : ℂ} (hs : (3 / 2 : ℝ) < s.re) : LSeriesSummable sqrtSeq s := by
  apply LSeriesSummable_of_le_const_mul_rpow hs
  refine ⟨1, fun n _ => ?_⟩
  change ‖(Real.sqrt (n : ℝ) : ℂ)‖ ≤ 1 * (n : ℝ) ^ ((3 / 2 : ℝ) - 1)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow]
  norm_num

/-- The actual Mathlib L-series of `C_d` converges absolutely for `Re(s) > 3/2`.
All hypotheses are arithmetic or the stated domain condition: no Hasse or
coefficient estimate is assumed. -/
theorem LFunction_cd_summable {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    {s : ℂ} (hs : (3 / 2 : ℝ) < s.re) :
    LSeriesSummable (fun n => (((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℤ) : ℂ)) s := by
  have hroot := sqrtSeq_summable hs
  have hmajor := hroot.convolution hroot
  apply Summable.of_norm_bounded hmajor.norm
  intro n
  by_cases hn : n = 0
  · subst hn; simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
    sqrtSeq_convolution]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  simpa only [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (show (0 : ℝ) ≤ (n.divisors.card : ℝ) by positivity)]
    using norm_LFunction_cd_le hd hsq n

end ZInQ.Contrib.Hasse
