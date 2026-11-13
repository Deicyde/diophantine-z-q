import ZInQKernel.Contrib.InertPrimes

/-!
P1 regression checks. After `lake build ZInQKernel`, run
`lake env lean scripts/check_inert_primes.lean`.

The affine count has no good-reduction or nonzero-d assumption. Only the
projective nonsingular point count needs good reduction. Mathlib's `LFunction`
comparison retains the original odd-squarefree hypotheses.
-/

namespace ZInQ.Contrib.InertPrimes

open ZInQ.Literature WeierstrassCurve

example (p d : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) :
    Nat.card {xy : ZMod p × ZMod p //
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} = p :=
  natCard_affine_cd_of_mod_four p d hp4

-- d = 0 is a singular cubic but still has exactly p affine solutions.
example : Nat.card {xy : ZMod 3 × ZMod 3 //
    xy.2 ^ 2 = xy.1 ^ 3 - (0 : ZMod 3) ^ 2 * xy.1} = 3 :=
  natCard_affine_cd_of_mod_four 3 0 (by norm_num)

-- The good-prime projective count includes the point at infinity.
example : Nat.card (shortCurve (-(5 : ZMod 3) ^ 2)).toAffine.Point = 4 :=
  natCard_cdPoint_of_mod_four_three 3 (by norm_num) (by norm_num)

example (d p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (hpd : ¬ p ∣ 2 * d) :
    cdEulerPoly d p = 1 + Polynomial.C (p : ℤ) * Polynomial.X ^ 2 :=
  cdEulerPoly_eq_one_add_of_mod_four_three d p hp4 hpd

example (d p : ℕ) (hd : Odd d) (hsq : Squarefree d) [Fact p.Prime]
    (hp4 : p % 4 = 3) : (shortCurve (-(d : ℚ) ^ 2)).LFunction p = 0 :=
  LFunction_cd_prime_eq_zero_of_mod_four_three hd hsq p hp4

-- This also covers the bad prime 3 of d = 3, without asserting ellipticity of the reduction.
example : (shortCurve (-(3 : ℚ) ^ 2)).LFunction 3 = 0 :=
  LFunction_cd_prime_eq_zero_of_mod_four_three (by decide) Nat.prime_three.squarefree 3
    (by norm_num)

#print axioms quadraticChar_sum_comp_of_odd
#print axioms natCard_affine_of_odd
#print axioms natCard_affine_cd_of_mod_four
#print axioms natCard_cdPoint_of_mod_four_three
#print axioms cdEulerPoly_eq_one_add_of_mod_four_three
#print axioms LFunction_cd_prime_eq_zero_of_mod_four_three_of_not_dvd
#print axioms LFunction_cd_prime_eq_zero_of_mod_four_three

end ZInQ.Contrib.InertPrimes
