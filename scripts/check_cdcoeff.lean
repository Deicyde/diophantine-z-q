import ZInQKernel.Contrib.CdCoeff

/-!
Regression checks and axiom report for issue #37, target P2.

Run after `lake build ZInQKernel`:

    lake env lean scripts/check_cdcoeff.lean

The examples deliberately quantify over every `d : ℕ`: the coefficient API
must not acquire oddness or squarefreeness assumptions. Only the comparison
with Mathlib's `LFunction` keeps its existing odd-squarefree hypotheses.
-/

namespace ZInQ.Contrib.CdCoeff

open ZInQ.Literature WeierstrassCurve

-- Zero, the empty Euler product, and the zeroth prime-power coefficient.
example (d : ℕ) : cdCoeff d 0 = 0 := by simp
example (d : ℕ) : cdCoeff d 1 = 1 := by simp
example (d p : ℕ) : cdCoeff d (p ^ 0) = 1 := by simp

-- Multiplicativity is valid even when one coprime input is zero.
example (d m n : ℕ) (h : m.Coprime n) :
    cdCoeff d (m * n) = cdCoeff d m * cdCoeff d n :=
  cdCoeff_mul_of_coprime d h

example (d : ℕ) : cdCoeff d (0 * 1) = cdCoeff d 0 * cdCoeff d 1 :=
  cdCoeff_mul_of_coprime d (by simp)

example (d : ℕ) : cdCoeff d (1 * 0) = cdCoeff d 1 * cdCoeff d 0 :=
  cdCoeff_mul_of_coprime d (by simp)

-- Prime-power normalization includes k = 0.
example (d p : ℕ) (hp : p.Prime) (k : ℕ) :
    cdCoeff d (p ^ k) =
      PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) :=
  cdCoeff_prime_pow d hp k

-- No oddness or squarefreeness restriction is needed for the recurrence.
example (d p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ 2 * d) (k : ℕ) :
    cdCoeff d (p ^ (k + 2)) =
      cdCoeff d p * cdCoeff d (p ^ (k + 1)) - (p : ℤ) * cdCoeff d (p ^ k) :=
  cdCoeff_prime_pow_recurrence hp hpd k

-- The point-count form has the same parameter scope.
example (d p : ℕ) [Fact p.Prime] (hpd : ¬ p ∣ 2 * d) (k : ℕ) :
    cdCoeff d (p ^ (k + 2)) =
      ((p : ℤ) + 1 - Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point) *
        cdCoeff d (p ^ (k + 1)) - (p : ℤ) * cdCoeff d (p ^ k) :=
  cdCoeff_prime_pow_recurrence_eq_sub_card p hpd k

-- The k = 0 specialization is the usual good-prime square coefficient.
example (d p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ 2 * d) :
    cdCoeff d (p ^ 2) = cdCoeff d p ^ 2 - (p : ℤ) := by
  simpa [pow_two] using cdCoeff_prime_pow_recurrence hp hpd 0

-- Bad-prime vanishing includes 2 and every positive prime power, not p^0.
example (k : ℕ) : cdCoeff 5 (2 ^ (k + 1)) = 0 :=
  cdCoeff_prime_pow_of_dvd 5 (by norm_num) (by norm_num) (by omega)

example (k : ℕ) : cdCoeff 5 (5 ^ (k + 1)) = 0 :=
  cdCoeff_prime_pow_of_dvd 5 (by norm_num) (by norm_num) (by omega)

-- The degenerate parameter d = 0 is covered by the coefficient definition.
example (p : ℕ) (hp : p.Prime) (k : ℕ) : cdCoeff 0 (p ^ (k + 1)) = 0 :=
  cdCoeff_prime_pow_of_dvd 0 hp (by simp) (by omega)

example (d p n : ℕ) (hp : p.Prime) (hpd : p ∣ 2 * d) (hn : p ∣ n) :
    cdCoeff d n = 0 :=
  cdCoeff_eq_zero_of_dvd d hp hpd hn

-- The comparison is for all indices n, including n = 0.
example (d : ℕ) (hd : Odd d) (hsq : Squarefree d) (n : ℕ) :
    cdCoeff d n = (shortCurve (-(d : ℚ) ^ 2)).LFunction n :=
  cdCoeff_eq_LFunction hd hsq n

-- Every declaration introduced by Core.lean, including the arithmetic-function wrapper.
#print axioms coeff_zero_invOfUnit_cdEulerPoly
#print axioms invOfUnit_cdEulerPoly_of_dvd
#print axioms cdCoeff_zero
#print axioms cdCoeff_one
#print axioms cdCoeff_of_ne_zero
#print axioms cdCoeff_mul_of_coprime
#print axioms cdArith
#print axioms cdArith_apply
#print axioms isMultiplicative_cdArith
#print axioms cdCoeff_prime_pow
#print axioms cdCoeff_prime_cdModel
#print axioms cdCoeff_prime
#print axioms cdCoeff_prime_of_dvd
#print axioms cdCoeff_prime_of_not_dvd
#print axioms cdCoeff_prime_eq_sub_card
#print axioms cdCoeff_prime_pow_of_dvd
#print axioms cdCoeff_eq_zero_of_dvd
#print axioms cdCoeff_eq_LFunction
#print axioms cdArith_eq_LFunction

#print axioms cdCoeff_prime_pow_recurrence
#print axioms cdCoeff_prime_pow_recurrence_eq_sub_card
#print axioms cdCoeff_prime_pow_succ_of_dvd

end ZInQ.Contrib.CdCoeff
