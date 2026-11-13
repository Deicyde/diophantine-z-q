import ZInQKernel.Contrib.BadPrimes

/-!
P3 regression and axiom checks. After `lake build ZInQKernel`, run
`lake env lean scripts/check_bad_primes.lean`.

Counts are for all affine solutions, including singular points. They must not
be confused with the nonsingular WeierstrassCurve point type.
-/

namespace ZInQ.Contrib.BadPrimes

open ZInQ.Literature WeierstrassCurve

-- The cusp parametrization works in every characteristic, including 2.
example (F : Type*) [Field F] [Fintype F] :
    Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3} = Fintype.card F :=
  natCard_affine_cusp F

-- Binary count for all d, without parity or squarefreeness assumptions.
example (d : ℕ) : Nat.card {xy : ZMod 2 × ZMod 2 //
    xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod 2) ^ 2 * xy.1} = 2 :=
  natCard_affine_cd_two d

example : Nat.card {xy : ZMod 3 × ZMod 3 //
    xy.2 ^ 2 = xy.1 ^ 3 - (0 : ZMod 3) ^ 2 * xy.1} = 3 :=
  natCard_affine_cd_of_dvd 0 3 (by simp)

example : Nat.card {xy : ZMod 5 × ZMod 5 //
    xy.2 ^ 2 = xy.1 ^ 3 - (5 : ZMod 5) ^ 2 * xy.1} = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact natCard_affine_cd_of_dvd 5 5 (by norm_num)

-- Even d is covered by the affine count, not by the LFunction model comparison.
example : Nat.card {xy : ZMod 2 × ZMod 2 //
    xy.2 ^ 2 = xy.1 ^ 3 - (2 : ZMod 2) ^ 2 * xy.1} = 2 :=
  natCard_affine_cd_two 2

example (d p : ℕ) [Fact p.Prime] (hbad : p ∣ 2 * d) :
    Nat.card {xy : ZMod p × ZMod p //
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} = p :=
  natCard_affine_cd_of_dvd d p hbad

-- The coefficient formula no longer requires a good-prime assumption.
example (d p : ℕ) (hd : Odd d) (hsq : Squarefree d) [Fact p.Prime] :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      (p : ℤ) - Nat.card {xy : ZMod p × ZMod p //
        xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} :=
  LFunction_cd_prime_eq_sub_card_all hd hsq p

example : (shortCurve (-(3 : ℚ) ^ 2)).LFunction 2 =
    (2 : ℤ) - Nat.card {xy : ZMod 2 × ZMod 2 //
      xy.2 ^ 2 = xy.1 ^ 3 - (3 : ZMod 2) ^ 2 * xy.1} :=
  LFunction_cd_prime_eq_sub_card_all (by decide) Nat.prime_three.squarefree 2

#print axioms affineCuspEquiv
#print axioms affineSquareTwoEquiv
#print axioms natCard_affine_cusp
#print axioms natCard_affine_cd_two
#print axioms natCard_affine_cd_of_dvd
#print axioms LFunction_cd_prime_eq_sub_card_of_dvd
#print axioms LFunction_cd_prime_eq_sub_card_all

end ZInQ.Contrib.BadPrimes
