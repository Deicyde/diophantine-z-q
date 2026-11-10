# Proposition D in full: the good slope primes have positive density

Status: research note, 2026-11-09. Each claim carries a mark:
**VERIFIED** (checked against the manuscript, the Lean source or Mathlib, or by a computation, which is
cited), **STANDARD** (a published theorem whose statement was checked to apply; reference given),
**SPECULATIVE** (an idea, unproved) or **UNCHECKED** (a source that could not be read; the statement is
quoted from memory and must be checked before use). Manuscript line numbers refer to `diophantine_zq.tex`
(11/5 version). Mathlib means the pinned revision `56a005855ea1` (Lean 4.35.0). PrimeNumberTheoremAnd
means the tag `v4.34.0` (commit `c39a7511`). Scripts and their outputs are in `scratch/pd-paper/`.

Notation. `G = {p : ZInQ.GoodSlopePrime p}`. For an odd prime `p`, `χ = χ_p` is the quadratic character
of `𝔽_p` (Mathlib `quadraticChar (ZMod p)`), and for `a ∈ 𝔽_p`

  `φ_p(a) = Σ_{x∈𝔽_p} χ(x³ + ax) ∈ ℤ`.

`π(N)` is the number of primes `≤ N`, `θ_S(N) = Σ_{p∈S, p≤N} log p` and, for `x > 1`,
`Φ_S(x) = Σ_{p∈S} (log p)/p^x`. Letters `ℓ` and `q` always denote primes.

## Summary

1. **Target.** `G` has positive relative upper density:
   `∃ c > 0, ∃ᶠ N in atTop, c·π(N) ≤ #(G ∩ [0, N])` (`GTSearch.PrimesRelUpperDensityPos`, the hypothesis
   of Green–Tao 2008, Theorem 1.2). It is deduced from a positive lower Dirichlet density:
   `liminf_{x→1⁺} (x − 1)Φ_G(x) > 0` (Theorem D, §5). The implication from Dirichlet density to upper
   density is Proposition 5.1. It needs only Abel summation and Chebyshev's bound `π(N) ≪ N/log N`.
2. **The arithmetic description needs no CM theory** (§1). For `p ≡ 1 (mod 8)` with `(p/7) = −1`, put
   `c_p = φ_p(1)/2`. Then `p = c_p² + e_p²` with `c_p` odd, the two point counts in `GoodSlopePrime`
   are `p + 1 ∓ 2c_p`, and their gcd is exactly `4·gcd(c_p, p + 1)`. The proof uses only elementary
   character sums: the substitution `x ↦ kx`, one involution `x ↦ −D²/x`, and Jacobsthal's identity
   `φ_p(1)² + φ_p(r)² = 4p`. The endomorphism ring, Tate modules, the Hasse bound and Jacobi sums are
   all avoided. An odd prime dividing `gcd(c_p, p + 1)` is `≡ 1 (mod 4)`.
   VERIFIED (by hand, and by computation for every prime below `2·10⁴`, resp. `3·10⁴`).
3. **The "Frobenius" conditions are congruences** (§2). The only Chebotarev-type conditions are
   `p ≡ 1 (mod 8)` and `p mod 7 ∈ {3, 5, 6}`. They are conditions in the abelian field `ℚ(ζ₈, √7)`, so
   Dirichlet's theorem for residue classes suffices. Mathlib has it in exactly the needed form,
   `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`. Neither Chebotarev, nor Hecke for
   `ℚ(i)`, nor Artin induction is needed (§3). The chosen subset is
   `G*_L = C_L ∖ T_L`, where `C_L` is the set of primes with `p ≡ 1 (mod 8)`, `p mod 7 ∈ {3, 5, 6}` and
   `p ≢ 0, −1 (mod ℓ)` for every prime `5 ≤ ℓ ≤ L` with `ℓ ≡ 1 (mod 4)`, and `T_L` is the set of primes
   bad at some `ℓ > L`. Its Dirichlet density is at least
   `δ_L − α_L`, where `δ_L ≥ 3/(8(L − 1))` and `α_L ≤ 5.6·A₁/(L log L)`.
4. **The tail is the one deep-ish step** (§4). For `L < ℓ ≤ N^{1/4}` one needs
   `#{p ≤ N bad at ℓ} ≤ A₁N/(ℓ² log N)` uniformly in `ℓ`. I prove it with `A₁ = 16003` by a
   two-dimensional Selberg sieve on the lattice coset `{(ℓU, b + ℓV)}`, with sifting density
   `ν(q) = (2q − 1)/q²` for `q ≡ 1 (mod 4)`. The bound for the Selberg sum `S ≫ log N` is proved by an
   elementary comparison with `Σ r(n)/n` (no Mertens theorem, no `L(1, χ₄)` evaluation). For
   `ℓ > N^{1/4}` a lattice count gives `O(N^{3/4})`. Trivial counting cannot replace the sieve (§4.1),
   and no choice of `G*` avoids it (§4.6). PrimeNumberTheoremAnd's `SelbergSieve.selberg_bound_simple`
   (sorry-free, built on Mathlib's `BoundingSieve`) is the closed Selberg bound this needs.
5. **Lean plan** (§6). Nine files, about 3.5–5.5k lines. That is less than earlier estimates, because the
   CM step shrinks to a few hundred lines of character sums. The hard part is the sieve instance
   (§4.3–4.5). A conditional theorem `goodPrimeDensity_of_uniformBadBound`, with the sieve bound as its
   only hypothesis, isolates it. The first step is Proposition 1.6 in Lean, which removes the most
   specialised piece of the earlier plan.

---

## 0. The target statements

The hypothesis to be discharged is `ZInQ.GoodPrimeAP` (`ZInQKernel/Hypotheses/PrimeAP.lean`). Its
derivation from Green–Tao 2008, Theorem 1.2, is written in `scratch/gt-search/GreenTaoReduction.lean`
(branch `wip/gt-search`; it compiles against our Mathlib, VERIFIED there). That file defines

```lean
def PrimesRelUpperDensityPos (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ N in atTop,
    c * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)
```

and proves `progressions_above_of_greenTaoDense`: if Green–Tao's Theorem 1.2 holds (`GreenTaoDense`), and
`G` consists of primes and satisfies `PrimesRelUpperDensityPos`, then `GoodPrimeAP` holds. So the
statement to prove is

> **Proposition D (weak form).** `PrimesRelUpperDensityPos {p | ZInQ.GoodSlopePrime p}`.

It will be derived from

> **Theorem D.** There are `L` and `η > 0` such that `(x − 1)·Φ_{G*_L}(x) ≥ η` for all `x ∈ (1, x₀]`,
> for some `x₀ > 1`. In particular `liminf_{x→1⁺}(x − 1)Φ_G(x) > 0`.

through Proposition 5.1 (Dirichlet density ⇒ upper natural density). Theorem D gives a lower
Dirichlet density in the von Mangoldt normalisation. The classical normalisation
`Σ_{p∈G} p^{−x}/log(1/(x − 1))` is equivalent for this purpose (Remark 5.2). The full Proposition D of
`nt-22p.md` §2.2 (natural density equal to `(1/8)∏_{ℓ≡1 (4)}(1 − 2/(ℓ − 1)²) ≈ 0.1060`) needs Hecke's
theorem for `ℚ(i)`. It is not needed for `GoodPrimeAP` (§3.1).

