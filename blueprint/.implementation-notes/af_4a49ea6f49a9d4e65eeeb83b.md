# Implementation note: The trivial point count

- Lean name: `ZInQ.Size.card_points_le`, `ZInQ.Size.addOrderOf_le_two_card_add_one`,
  `ZInQ.Size.odd_prime_count_bounds`.
- Draft:
  ```lean
  theorem card_points_le {k : Type*} [Field k] [Fintype k] [DecidableEq k] (h2 : (2 : k) ≠ 0) (a : k) :
      Nat.card (shortCurve a).toAffine.Point ≤ 2 * Fintype.card k + 1
  theorem addOrderOf_le_two_card_add_one ... (P : (shortCurve a).toAffine.Point) :
      addOrderOf P ≤ 2 * Fintype.card k + 1
  theorem odd_prime_count_bounds {p : ℕ} (hp : 3 ≤ p) : 2 * p ^ 2 + 1 ≤ p ^ 6 ∧ (2 * p + 1) ^ 2 ≤ p ^ 6
  ```
- Proof: inject `Point` into `Option (k × k)` (Mathlib `Point.some` data); for fixed `x` the `y`
  with `y^2 = c` form a set of card ≤ 2 (`Commute.sq_eq_sq_iff_eq_or_eq_neg`,
  Mathlib/Algebra/Ring/Commute.lean:125, or `Polynomial.card_roots'`);
  `Finset.card_le_mul_card_image` (Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:408) for
  the fibres over `x`. Then `addOrderOf_le_card` (to_additive of `orderOf_le_card`,
  Mathlib/GroupTheory/OrderOfElement.lean:968). The numeric part by `nlinarith`/`Nat.pow_le_pow_left`.
  `Finite`/`Fintype` instance on `Point` over a finite field: build from the injection.
- Finite computation: no.
- Upstream reuse: none.
- Difficulty: low-medium (~80 lines).

Shared design (formal-multiple notes): work on `K₀ = QuadraticAlgebra ℚ 2 0` and the model
chapter's integer ring `Zs` (`QuadraticAlgebra ℤ 2 0`, a PID by the model chapter). Valuations at
a prime: `IsDedekindDomain.HeightOneSpectrum.valuation` (Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:322,
values in `ℤᵐ⁰`), or an additive wrapper `vP 𝔭 : K₀ → WithTop ℤ`; at `(s)` reuse the model
chapter's `vS` and its formula `ZInQ.val_s_formula`. Points: `genCurve.toAffine.Point` and
`ZInQ.genP0` (model chapter). No completion of `K₀` is needed anywhere: every statement is
about valuations on `K₀` itself.
