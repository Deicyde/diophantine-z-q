/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- A Mathlib lemma used by the Tau Ceti nov01 (97a5b23586f9) modules and absent from the pinned
-- Mathlib 56a00585 (it is in later Mathlib under this name). Proof written for this backport.
module

public import Mathlib.Algebra.Polynomial.Coeff

public section

namespace Polynomial

/-- `X ^ n - X` is nonzero for `n > 1`. -/
theorem X_pow_sub_X_ne_zero {R : Type*} [Ring R] [Nontrivial R] {n : ℕ} (hn : 1 < n) :
    (X ^ n - X : R[X]) ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : R[X] ↦ p.coeff n) h
  simp only [coeff_sub, coeff_X_pow_self, coeff_X, coeff_zero] at h1
  rw [if_neg hn.ne, sub_zero] at h1
  exact one_ne_zero h1

end Polynomial

end
