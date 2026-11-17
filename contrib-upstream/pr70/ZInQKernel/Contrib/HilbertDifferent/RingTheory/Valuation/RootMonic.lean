/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Valuation/RootMonic.lean
Original SHA-256: 7fbf72cc8c2a2ad34e4751a66b652a7e64fdcaff2cdf182c9f95795082c303c8
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/Valuation/RootMonic.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace Valuation

open Polynomial

variable {L Γ : Type*} [Ring L] [LinearOrderedCommMonoidWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}

/- If two elements have value at most one and their product has value one, then the first
element has value one. -/
lemma map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  nontriviality Γ
  set n := p.natDegree with hn
  have h0 : ν t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (t ^ n) := by
    rw [map_pow]
    refine ν.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc ν (p.coeff i * t ^ i) ≤ 1 * ν t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_pow]

/- A root of a monic polynomial whose coefficients have value at most one also has value
at most one. -/
lemma le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (heq : p.eval t = 0) :
    ν t ≤ 1 := by
  nontriviality Γ
  by_contra! ht
  have h := ν.map_eval_eq_of_one_lt hp hcoeff ht
  rw [heq, map_zero] at h
  exact (pow_ne_zero _ (zero_lt_one.trans ht).ne') h.symm

section Quadratic

variable {c : L}

/- A monic quadratic with integral coefficients, evaluated at an element of value `> 1`, is
dominated by its leading term. -/
end Quadratic

section Cubic

variable {c : L}

-- After the subsingleton value-monoid case is discharged, `ν` supplies the nontriviality
-- of `L` needed to compute the degree and monicity of the cubic.

/- The non-leading coefficients of `X³ + aX² + bX + c` are `a`, `b`, `c` (and zeros), so they
are integral as soon as `a`, `b`, `c` are. This is the coefficient hypothesis that the general
lemmas above take. -/
end Cubic

end Valuation

end
