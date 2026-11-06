# Implementation note: Primes above an odd prime

- Lean name: `ZInQ.Size.primes_over_odd`.
- Draft:
  ```lean
  theorem primes_over_odd {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
      (∀ 𝔭 : Ideal Zs, 𝔭.IsPrime → (p : Zs) ∈ 𝔭 →
          Nat.card (Zs ⧸ 𝔭) ≤ p ^ 2 ∧ 𝔭.IsMaximal) ∧
      Set.ncard {𝔭 : Ideal Zs | 𝔭.IsPrime ∧ (p : Zs) ∈ 𝔭} ≤ 2 ∧
      (∀ 𝔭 : Ideal Zs, 𝔭.IsPrime → (p : Zs) ∈ 𝔭 → (p : Zs) ∉ 𝔭 ^ 2) ∧
      (∀ 𝔭 : Ideal Zs, 𝔭.IsPrime → (p : Zs) ∈ 𝔭 → 𝔭.map conjZs ∈ {𝔮 | 𝔮.IsPrime ∧ (p : Zs) ∈ 𝔮})
  ```
  plus the explicit description in the split case (`𝔭 = Ideal.span {p, s - r}` with residue map
  `a + b s ↦ a + b r`), which the extraction lemma uses through conjugation only.
- Mathlib: `Ideal.primesOver` (Mathlib/RingTheory/Ideal/Over.lean:376); the fundamental identity
  `Ideal.sum_ramification_inertia` (Mathlib/NumberTheory/RamificationInertia/Basic.lean:611) gives
  `Σ e f = 2`, hence at most two primes and `f ≤ 2`; unramifiedness for `p ∤ 8` via
  `NumberField.discr` is heavier than the direct route. Direct route (recommended):
  `Zs ⧸ (p) ≃ ZMod p[X] ⧸ (X^2 - 2)` and `ZMod.isSquare` / quadratic reciprocity is not needed —
  just case on `∃ r : ZMod p, r^2 = 2`; irreducibility of `X^2 - C 2` over `ZMod p` when there is
  no root, by `X_pow_sub_C_irreducible_of_prime` (Mathlib/FieldTheory/KummerPolynomial.lean:99,
  with the prime exponent `2`) or `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`
  (Mathlib/Algebra/Polynomial/SpecificDegree.lean:57). Kummer–Dedekind is available as `primesOverSpanEquivMonicFactorsMod`
  (Mathlib/NumberTheory/NumberField/Ideal/KummerDedekind.lean:169) but requires the `RingOfIntegers`
  setup; the model chapter's `Zs` is a `QuadraticAlgebra`, so the direct route is simpler.
- Finite computation: no.
- Upstream reuse: none.
- Difficulty: medium (~150 lines of ideal bookkeeping).

Shared design (formal-multiple notes): work on `K₀ = QuadraticAlgebra ℚ 2 0` and the model
chapter's integer ring `Zs` (`QuadraticAlgebra ℤ 2 0`, a PID by the model chapter). Valuations at
a prime: `IsDedekindDomain.HeightOneSpectrum.valuation` (Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:322,
values in `ℤᵐ⁰`), or an additive wrapper `vP 𝔭 : K₀ → WithTop ℤ`; at `(s)` reuse the model
chapter's `vS` and its formula `ZInQ.val_s_formula`. Points: `genCurve.toAffine.Point` and
`ZInQ.genP0` (model chapter). No completion of `K₀` is needed anywhere: every statement is
about valuations on `K₀` itself.
