/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.GroupTheory.OrderOfElement.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.GroupTheory.OrderOfElement.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.GroupTheory.OrderOfElement.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Totient
public import ZInQKernel.Contrib.TauCeti.Data.Nat.Factorization.MulDvd
import Mathlib.FieldTheory.Finite.Basic

public section

namespace TauCeti

/-- If `x ^ n = 1` in a monoid, then every power `x ^ d` is killed by the `(n / gcd(n, d))`-th
power map: `(x ^ d) ^ (n / gcd(n, d)) = 1`. In a group of order `N` this applies with `n = N`
(Mathlib's `pow_card_eq_one'`). -/
@[to_additive nsmul_nsmul_div_gcd_eq_zero
/-- If `n • x = 0` in an additive monoid, then every multiple `d • x` is killed by multiplication
by `n / gcd(n, d)`: `(n / gcd(n, d)) • d • x = 0`. -/]
theorem pow_pow_div_gcd_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hx : x ^ n = 1) (d : ℕ) :
    (x ^ d) ^ (n / n.gcd d) = 1 := by
  -- `d * (n / g) = n * (d / g)` with `g = gcd(n, d)` dividing both `n` and `d`.
  rw [← pow_mul, ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm d,
    Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), pow_mul, hx, one_pow]

end TauCeti

end
