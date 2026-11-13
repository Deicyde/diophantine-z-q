import ZInQKernel.Contrib.CdCoeff.Core

/-!
# Prime-power recurrences for the coefficients of `C_d`

These identities follow directly from `cdEulerPoly`, so they hold for every natural `d`.
No oddness or squarefreeness assumption is needed. At a good prime the inverse Euler
factor satisfies the usual second-order recurrence; at a bad prime it is the constant
series `1`, and all positive prime-power coefficients vanish.
-/

namespace ZInQ.Contrib.CdCoeff

open ZInQ.Literature WeierstrassCurve ArithmeticFunction

/-- At a good prime, the prime-power coefficients satisfy the recurrence with
`a_p = p + 1 - #C_d(𝔽_p)` (including the point at infinity). -/
theorem cdCoeff_prime_pow_recurrence_eq_sub_card {d : ℕ} (p : ℕ) [hp : Fact p.Prime]
    (hpd : ¬ p ∣ 2 * d) (k : ℕ) :
    cdCoeff d (p ^ (k + 2)) =
      ((p : ℤ) + 1 - Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point) *
        cdCoeff d (p ^ (k + 1)) - (p : ℤ) * cdCoeff d (p ^ k) := by
  rw [cdCoeff_prime_pow d hp.out, cdCoeff_prime_pow d hp.out, cdCoeff_prime_pow d hp.out]
  set F : PowerSeries ℤ := PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1
  have h0 : PowerSeries.constantCoeff (cdEulerPoly d p : PowerSeries ℤ) =
      ((1 : ℤˣ) : ℤ) := by
    simpa using cdEulerPoly_coeff_zero d p
  have hmul : F * (cdEulerPoly d p : PowerSeries ℤ) = 1 :=
    PowerSeries.invOfUnit_mul (cdEulerPoly d p : PowerSeries ℤ) 1 h0
  have h := congrArg (PowerSeries.coeff (k + 2)) hmul
  have hP : (cdEulerPoly d p : PowerSeries ℤ) =
      1 - PowerSeries.C ((p : ℤ) + 1 -
        Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point) * PowerSeries.X +
      PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2 := by
    simp only [cdEulerPoly, ite_eq_right hpd, Polynomial.coe_add, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
      Polynomial.coe_pow, cdModel_eq_shortCurve]
  rw [hP, mul_add, mul_sub, mul_one, map_add, map_sub] at h
  simp only [← mul_assoc, PowerSeries.coeff_succ_mul_X,
    PowerSeries.coeff_mul_X_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_one,
    show k + 2 ≠ 0 by omega, ite_false] at h
  linarith

/-- At a good prime, the recurrence may be written using `cdCoeff d p` itself. -/
theorem cdCoeff_prime_pow_recurrence {d p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ 2 * d) (k : ℕ) :
    cdCoeff d (p ^ (k + 2)) =
      cdCoeff d p * cdCoeff d (p ^ (k + 1)) - (p : ℤ) * cdCoeff d (p ^ k) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [cdCoeff_prime_of_not_dvd d p hpd]
  exact cdCoeff_prime_pow_recurrence_eq_sub_card p hpd k

/-- At a prime dividing `2d`, every positive prime-power coefficient vanishes. -/
theorem cdCoeff_prime_pow_succ_of_dvd {d p : ℕ} (hp : p.Prime)
    (hpd : p ∣ 2 * d) (k : ℕ) : cdCoeff d (p ^ (k + 1)) = 0 :=
  cdCoeff_prime_pow_of_dvd d hp hpd (Nat.succ_ne_zero k)

end ZInQ.Contrib.CdCoeff
