# Explicit identities in K0 (explicit-identities)

- Lean name: `ZInQ.k0_identities` (one conjunction), plus named projections used downstream:
  `ZInQ.genD_sq`, `ZInQ.norm_genD`, `ZInQ.epsilon_pow_four`, `ZInQ.epsilon_pow_six`,
  `ZInQ.genD_mul_epsilon_pow_four`, `ZInQ.delta_sq`, `ZInQ.norm_delta`, and the real-sign
  corollaries `ZInQ.totallyPositive_genD`, `ZInQ.totallyPositive_delta`, `ZInQ.signVec_epsilon`,
  `ZInQ.embPlus_delta_mem`, `ZInQ.embMinus_delta_mem` (`σ(δ) ∈ Set.Icc 1 5`).
- Draft (K0 = `QuadraticAlgebra ℚ 2 0`, elements written `⟨re, im⟩`):
  ```lean
  theorem k0_identities :
      genD ^ 2 = (⟨11243, -7950⟩ : K0) ∧ QuadraticAlgebra.norm genD = 7 ∧
      (⟨1, 1⟩ : K0) * ⟨-1, 1⟩ = 1 ∧ (⟨1, 1⟩ : K0) ^ 4 = ⟨17, 12⟩ ∧ (⟨1, 1⟩ : K0) ^ 6 = ⟨99, 70⟩ ∧
      genD * (⟨1, 1⟩ : K0) ^ 4 = ⟨3, -1⟩ ∧ (⟨3, -1⟩ : K0) ^ 2 = ⟨11, -6⟩ ∧
      QuadraticAlgebra.norm (⟨3, -1⟩ : K0) = 7 ∧ QuadraticAlgebra.norm (⟨0, 1⟩ : K0) = -2 ∧
      (2 * 53 ^ 2 < 75 ^ 2 : Prop) ∧ 2 ^ 6 * 7 ^ 4 = 392 ^ 2 ∧ 7 ^ 2 < 392 ∧ 676 = 26 ^ 2
  ```
  Integer parts over `ℕ`/`ℤ` by `decide`; K0 parts by `ext <;> norm_num [pow_succ]` (component
  arithmetic on small rationals). Totally-positive criterion: `0 < u ∧ 2 * v ^ 2 < u ^ 2 →
  0 < u + v * Real.sqrt 2 ∧ 0 < u - v * Real.sqrt 2` via `Real.sq_sqrt`, `abs_lt`, `nlinarith`.
- Upstream reuse: `ZInQ.ModelCoordinates.epsilon_inverse`, `delta_identity` (lean/ZInQ/ModelCoordinateIdentities.lean)
  give items 2-3 over any char-0 field with `s ^ 2 = 2`; instantiate at `K := K0`, `s := sqrt2`.
- FINITE COMPUTATION: yes. Closed decidable form above. Method: kernel `decide` for the integer
  comparisons (instant) and `norm_num` for the K0 identities; no `native_decide` and no
  certificate needed at any stage.
- Consumers: generator-curve, units, special-primes, coordinate-change, odd-free-index,
  duplication-archimedean, duplication-common-divisor, duplication-height-bounds.
- Difficulty: easy.
