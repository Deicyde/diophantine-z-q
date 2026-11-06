# Implementation note: Reduction orders of P0

- Lean name: `ZInQ.Size.exists_reduction_multiple`.
- Draft:
  ```lean
  theorem exists_reduction_multiple (N : ℕ) (hN : 1 ≤ N) :
      ∃ m₀ : ℕ, 1 ≤ m₀ ∧ m₀ ≤ N ^ 6 ∧
        ∀ p ∈ N.primeFactors, p ≠ 2 → ∀ 𝔭 ∈ primesAbove p,
          (m₀ : ℤ) • genP0 ∈ E1sub 𝔭 (-genDZs ^ 2)
  ```
- Construction: `m₀ := ∏ p ∈ N.primeFactors.filter (· ≠ 2), ∏ 𝔭 ∈ (primesAbove p).toFinset,
  addOrderOf (reductionHom 𝔭 _ ⟨genP0, _⟩)`. Divisibility of each factor into `m₀`
  (`Finset.dvd_prod_of_mem`), `addOrderOf_dvd_iff_nsmul_eq_zero`, kernel = `E1sub`.
  Bound: per `p`, `∏ ≤ p^6` from the trivial point count and the residue-field cardinalities
  (`primes_over_odd`), then `∏_{p ∣ N} p^6 ≤ N^6` from `Nat.prod_primeFactors_dvd`
  (Mathlib/Data/Nat/Factorization/Basic.lean:349) and `Nat.le_of_dvd`, using
  `∏ p^6 = (∏ p)^6` (`Finset.prod_pow`).
- Mathlib: `Nat.primeFactors`, `Finset.prod_pow`, `Finset.dvd_prod_of_mem`, `addOrderOf`,
  `addOrderOf_dvd_iff_nsmul_eq_zero`, `Nat.le_of_dvd`.
- Finite computation: no.
- Upstream reuse: none.
- Difficulty: medium (~120 lines; mostly finiteness of the set of primes above `p` as a Finset).

Shared design (formal-multiple notes): work on `K₀ = QuadraticAlgebra ℚ 2 0` and the model
chapter's integer ring `Zs` (`QuadraticAlgebra ℤ 2 0`, a PID by the model chapter). Valuations at
a prime: `IsDedekindDomain.HeightOneSpectrum.valuation` (Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:322,
values in `ℤᵐ⁰`), or an additive wrapper `vP 𝔭 : K₀ → WithTop ℤ`; at `(s)` reuse the model
chapter's `vS` and its formula `ZInQ.val_s_formula`. Points: `genCurve.toAffine.Point` and
`ZInQ.genP0` (model chapter). No completion of `K₀` is needed anywhere: every statement is
about valuations on `K₀` itself.
