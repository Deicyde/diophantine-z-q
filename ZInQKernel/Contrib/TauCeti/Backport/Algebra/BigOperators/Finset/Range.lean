/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.Algebra.BigOperators.Finset.Range), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.Algebra.BigOperators.Finset.Range`.
module

public import ZInQKernel.Contrib.TauCeti.Algebra.BigOperators.Finset.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

public section

section
namespace Finset

/-- A product over `range (n * q)` is the product of `q` consecutive blocks of `n` factors. -/
@[to_additive sum_range_mul_eq_sum_sum
  /-- A sum over `range (n * q)` is the sum of `q` consecutive blocks of `n` terms. -/]
theorem prod_range_mul_eq_prod_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (n q : ℕ) :
    ∏ l ∈ range (n * q), f l = ∏ j ∈ range q, ∏ l ∈ range n, f (n * j + l) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, prod_range_add, ih, prod_range_succ]

end Finset
end

end
