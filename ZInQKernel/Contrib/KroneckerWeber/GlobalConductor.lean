/-
Positive conductor arithmetic for the global Kronecker–Weber degree comparison.
Only finite products of distinct rational primes are used. No local extension
or conductor-existence theorem is assumed or proved in this arithmetic module.
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Prime-power conductor products

This supplies the precise Euler-totient product in the global degree squeeze.
The prime `2`, exponent zero and empty index set are included. It is not a
proof that an arbitrary abelian field has the necessary local conductor exponents.
-/

public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber

/-- Distinct rational prime powers are coprime, including exponent zero. -/
theorem prime_powers_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (r s : ℕ) : (p ^ r).Coprime (q ^ s) :=
  ((Nat.coprime_primes hp hq).mpr hpq).pow_left r |>.pow_right s

/-- The selected prime-power product is positive even for zero exponents and an
empty finite set. No zero cyclotomic level can be manufactured by this product. -/
theorem prime_power_conductor_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ → ℕ) :
    0 < ∏ p ∈ S, p ^ r p :=
  Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)

/-- The Euler totient of the positive product of distinct rational prime powers
is the product of their Euler totients, with no omitted factor at `2`. -/
theorem totient_prime_power_conductor (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (r : ℕ → ℕ) :
    (∏ p ∈ S, p ^ r p).totient = ∏ p ∈ S, (p ^ r p).totient := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hSP : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : (p ^ r p).Coprime (∏ q ∈ S, q ^ r q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact prime_powers_coprime hp (hSP q hq) (fun h => hpS (h ▸ hq)) _ _
    rw [Finset.prod_insert hpS, Nat.totient_mul hcop,
      Finset.prod_insert hpS, ih hSP]

end ZInQ.Contrib.KroneckerWeber
