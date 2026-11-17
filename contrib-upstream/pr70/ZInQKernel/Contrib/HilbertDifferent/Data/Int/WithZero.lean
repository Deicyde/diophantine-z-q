/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/Data/Int/WithZero.lean
Original SHA-256: f1380afddf93310d81d8c3e6f9d81cb1c53cef8266ea2aeb7513700d39d3b492
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
TauCeti/Data/Int/WithZero.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Int.WithZero
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open Multiplicative WithZero
open scoped NNRat

namespace WithZeroMulInt

/- The monoid-with-zero homomorphism `ℤᵐ⁰ → ℚ≥0` sending a nonzero exponent `n` to `e ^ n`.

This is the nonnegative-rational counterpart of Mathlib's `WithZeroMulInt.toNNReal`. -/
def toNNRat {e : ℚ≥0} (he : e ≠ 0) : ℤᵐ⁰ →*₀ ℚ≥0 where
  __ := WithZero.lift' <|
    (Units.coeHom ℚ≥0).comp <| zpowersHom ℚ≥0ˣ (Units.mk0 e he)

/- On a finite exponent, `toNNRat` is the corresponding integer power of its base. -/
@[simp]
theorem toNNRat_coe {e : ℚ≥0} (he : e ≠ 0) (n : Multiplicative ℤ) :
    toNNRat he (n : ℤᵐ⁰) = e ^ n.toAdd := by
  simp [toNNRat]

/- The value of `toNNRat` at a nonzero exponent is the corresponding integer power. -/
theorem toNNRat_strictMono {e : ℚ≥0} (he : 1 < e) :
    StrictMono (toNNRat he.ne_zero) := by
  intro x y hxy
  cases y
  · exact (not_lt_of_ge bot_le hxy).elim
  cases x
  · simpa using zpow_pos he.pos _
  · rw [toNNRat_coe, toNNRat_coe]
    exact (zpow_right_strictMono₀ he) <|
      Multiplicative.toAdd_lt.mpr (WithZero.coe_lt_coe.mp hxy)

/- For a base different from zero and one, `toNNRat` takes the value one only at exponent
one, which represents the integer exponent zero in `ℤᵐ⁰`. -/
theorem toNNRat_le_one_iff {e : ℚ≥0} {x : ℤᵐ⁰} (he : 1 < e) :
    toNNRat he.ne_zero x ≤ 1 ↔ x ≤ 1 := by
  rw [← (toNNRat_strictMono he).le_iff_le, map_one]

end WithZeroMulInt
