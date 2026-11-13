import ZInQKernel.RouteK.Rank.LFunctionCd
import ZInQKernel.Contrib.InertPrimes.PointCount

/-!
# P1: vanishing coefficients at primes congruent to 3 modulo 4

The affine count applies to every `d`. At primes of good reduction, adding the
point at infinity gives `#C_d(𝔽_p) = p + 1`. The resulting coefficient of
Mathlib's `LFunction` is zero for odd squarefree `d`; the bad-prime case is
already zero by the existing additive-reduction computation.
-/

namespace ZInQ.Contrib.InertPrimes

open ZInQ.Literature WeierstrassCurve

/-- At a good prime congruent to `3 mod 4`, the congruent-number curve has `p + 1` points. -/
theorem natCard_cdPoint_of_mod_four_three {d : ℕ} (p : ℕ) [Fact p.Prime]
    (hp4 : p % 4 = 3) (hpd : ¬ p ∣ 2 * d) :
    Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point = p + 1 := by
  rw [natCard_point_shortCurve_zmod p hpd, natCard_affine_cd_of_mod_four p d hp4]

/-- The good-prime Euler polynomial has no linear term when `p ≡ 3 mod 4`. -/
theorem cdEulerPoly_eq_one_add_of_mod_four_three (d p : ℕ) [Fact p.Prime]
    (hp4 : p % 4 = 3) (hpd : ¬ p ∣ 2 * d) :
    cdEulerPoly d p = 1 + Polynomial.C (p : ℤ) * Polynomial.X ^ 2 := by
  have hcard := natCard_cdPoint_of_mod_four_three p hp4 hpd
  simp [cdEulerPoly, hpd, cdModel_eq_shortCurve, hcard]

/-- The good-prime coefficient is zero at primes congruent to `3 mod 4`. -/
theorem LFunction_cd_prime_eq_zero_of_mod_four_three_of_not_dvd {d : ℕ}
    (hd : Odd d) (hsq : Squarefree d) (p : ℕ) [Fact p.Prime]
    (hp4 : p % 4 = 3) (hpd : ¬ p ∣ 2 * d) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p = 0 := by
  rw [LFunction_cd_apply_prime_eq_sub_card hd hsq p hpd,
    natCard_affine_cd_of_mod_four p d hp4, sub_self]

/-- Including bad primes, every prime congruent to `3 mod 4` has coefficient zero. -/
theorem LFunction_cd_prime_eq_zero_of_mod_four_three {d : ℕ}
    (hd : Odd d) (hsq : Squarefree d) (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p = 0 := by
  by_cases hpd : p ∣ 2 * d
  · exact LFunction_cd_apply_prime_of_dvd hd hsq p hpd
  · exact LFunction_cd_prime_eq_zero_of_mod_four_three_of_not_dvd hd hsq p hp4 hpd

end ZInQ.Contrib.InertPrimes
