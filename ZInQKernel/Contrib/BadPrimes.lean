import ZInQKernel.RouteK.Rank.LFunctionCd
import ZInQKernel.Contrib.BadPrimes.Affine

/-!
# P3: the affine point-count formula at every prime

At a prime dividing `d` the affine equation is the cusp `y² = x³`, whose
solutions are parametrized by the field. At `p = 2`, squaring is the identity,
so the affine equation is a graph over `x`. Both counts are `p`, agreeing
with the existing zero coefficient at every prime dividing `2*d`.

These are counts of all affine solutions, including singular ones. They are
not counts of Mathlib's nonsingular `WeierstrassCurve.Affine.Point` type.
-/

namespace ZInQ.Contrib.BadPrimes

open ZInQ.Literature WeierstrassCurve

/-- For every `d`, a prime dividing `2*d` has exactly `p` affine solutions. -/
theorem natCard_affine_cd_of_dvd (d p : ℕ) [Fact p.Prime] (hbad : p ∣ 2 * d) :
    Nat.card {xy : ZMod p × ZMod p //
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} = p := by
  have hprime : p.Prime := Fact.out
  rcases hprime.dvd_mul.mp hbad with hp2 | hpd
  · have hp : p = 2 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hp2
    subst p
    exact natCard_affine_cd_two d
  · have hd0 : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr hpd
    simpa [hd0, ZMod.card] using natCard_affine_cusp (ZMod p)

/-- The same affine point-count formula holds at bad primes for odd squarefree `d`. -/
theorem LFunction_cd_prime_eq_sub_card_of_dvd {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [Fact p.Prime] (hbad : p ∣ 2 * d) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      (p : ℤ) - Nat.card {xy : ZMod p × ZMod p //
        xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} := by
  rw [LFunction_cd_apply_prime_of_dvd hd hsq p hbad, natCard_affine_cd_of_dvd d p hbad,
    sub_self]

/-- **All primes**: the coefficient is `p` minus the number of all affine solutions. -/
theorem LFunction_cd_prime_eq_sub_card_all {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [Fact p.Prime] :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      (p : ℤ) - Nat.card {xy : ZMod p × ZMod p //
        xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} := by
  by_cases hbad : p ∣ 2 * d
  · exact LFunction_cd_prime_eq_sub_card_of_dvd hd hsq p hbad
  · exact LFunction_cd_apply_prime_eq_sub_card hd hsq p hbad

end ZInQ.Contrib.BadPrimes
