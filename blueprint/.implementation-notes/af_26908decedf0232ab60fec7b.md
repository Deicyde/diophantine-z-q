# Implementation note: Congruences for P0 modulo seven

- Lean name: `ZInQ.Size.bad_place_congruences`.
- FINITE COMPUTATION. Exact decidable form:
  ```lean
  theorem bad_place_congruences :
      (1641 - 1160 * 3 - 2 * 8 : ℤ) % 7 = 0 ∧ (-123720 + 87483 * 3 - 6 * 32 : ℤ) % 7 = 0 ∧
      (-11243 + 7950 * 3 : ℤ) % 7 = 0 ∧ (6 ^ 2 - 2 ^ 3 : ℤ) % 7 = 0 ∧
      (2 * 6 : ℤ) % 7 ≠ 0 ∧ (3 * 2 ^ 2 : ℤ) % 7 ≠ 0 ∧ (8 : ℤ) % 7 ≠ 0 ∧ (32 : ℤ) % 7 ≠ 0 := by
    decide
  ```
- Size: eight operations on integers below `3 * 10^5`.
- Method: kernel `decide` (`Int` arithmetic reduces through GMP-backed `Nat` literals). An
  equivalent statement in `ZMod 7` (`(1641 - 1160 * 3 : ZMod 7) = 2 * 8`, ...) is also `decide`-able
  and may be more convenient for the residue map `ZInQ.residueSeven` of the model chapter.
- Mathlib: none.
- Upstream reuse: none.
- Checked: this exact statement was elaborated with `lake env lean` (Lean 4.35.0, Mathlib v4.35.0) by the reviewer; `decide` succeeds.
- Difficulty: trivial.

Shared design (formal-multiple notes): work on `K₀ = QuadraticAlgebra ℚ 2 0` and the model
chapter's integer ring `Zs` (`QuadraticAlgebra ℤ 2 0`, a PID by the model chapter). Valuations at
a prime: `IsDedekindDomain.HeightOneSpectrum.valuation` (Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:322,
values in `ℤᵐ⁰`), or an additive wrapper `vP 𝔭 : K₀ → WithTop ℤ`; at `(s)` reuse the model
chapter's `vS` and its formula `ZInQ.val_s_formula`. Points: `genCurve.toAffine.Point` and
`ZInQ.genP0` (model chapter). No completion of `K₀` is needed anywhere: every statement is
about valuations on `K₀` itself.
