# pd-paper: Proposition D in full, and a Lean plan

Deliverable: `docs/research/pd-paper.md`. Log: `scratch/pd-paper/log.md`. Scripts:
`scratch/pd-paper/{lemmas,gcdformula,density,sieveaux}.py`.

## Summary

- **Target proved on paper.** `{p | GoodSlopePrime p}` has positive lower Dirichlet density, in the von
  Mangoldt normalisation (Theorem D, §5). This implies positive relative upper natural density, the
  hypothesis of Green–Tao 2008 Theorem 1.2 (Proposition 5.3, by discrete Abel summation and Chebyshev's
  bound; proved in the note). Every step is written out with explicit constants
  (`A₁ = 16003`, `N₁ = e^{1920}`, `L = e^{240045}`). The constants are absurd, but only positivity enters
  `GoodPrimeAP`.
- **The CM step needs no CM theory** (§1). For `p ≡ 1 (8)` with `(p/7) = −1`, let `c_p = φ_p(1)/2`, with
  `φ_p(a) = Σ_x χ(x³ + ax)`. The two point counts are `p + 1 ∓ 2c_p`, and their gcd is exactly
  `4·gcd(c_p, p + 1)`. The proof uses scaling `φ(k²a) = χ(k)φ(a)`, one involution `x ↦ −D²/x` (giving
  `4 | #E`) and Jacobsthal's identity `φ(1)² + φ(r)² = 4p` (so `p = c_p² + e_p²`). No endomorphism ring, no
  Hasse bound, no Jacobi sums. Bad primes `ℓ` are `≡ 1 (4)`. VERIFIED by hand, and by computation against
  the literal Lean definition for every prime `< 2·10⁴`, plus the gcd formula for `p < 3·10⁴`.
- **The Frobenius conditions are congruences** (§2–3). The needed conditions live in the abelian field
  `ℚ(ζ₈, √7)`, so Mathlib's `LSeries_residueClass_lower_bound` suffices. Neither Chebotarev, nor Hecke for
  `ℚ(i)`, nor Artin induction is needed. The `D₄` field `ℚ(√2, √d, √d̄)` plays no role, because the gcd
  sees only `dd̄ = 7`.
- **The one genuinely analytic step is the tail** (§4): `#{p ≤ N bad at ℓ} ≤ A₁N/(ℓ² log N)` for
  `ℓ ≤ N^{1/4}`. It is proved by a two-dimensional Selberg sieve on the coset `(ℓU, b + ℓV)` with
  `ν(q) = (2q − 1)/q²` (`q ≡ 1 (4)`). The Selberg sum is bounded below elementarily: `R(w) = Σ r(n)/n ≥
  (2/3)log w − 2`, and a convolution `r ≤ h ∗ v` with `Σ v(m)/m ≤ 2ζ(2)⁴`. Large `ℓ` are handled by a
  lattice count. §4.6 examined the alternative choices of `G*`, and none avoids the sieve.
- **Numerics** (primes `≤ 10⁸`): `|G|/π = 0.10612` against the Euler product `0.10602`. `G*_L` matches
  its predicted density for `L = 5 … 1000`. Every bad `ℓ` is `≡ 1 (4)`. The empirical sieve constant is
  about `0.30`.

## Chosen route

Route DS: Dirichlet's theorem for residue classes (Mathlib) for the main term `δ_L ≥ 3/(8(L − 1))`, plus
the elementary character-sum description (§1), plus the Selberg sieve (PrimeNumberTheoremAnd's
`SelbergSieve.selberg_bound_simple`, sorry-free, built on Mathlib's `BoundingSieve`) for
`α_L ≤ 5.55A₁/(L log L)`.

## Lean plan (§6)

Nine files, `ZInQKernel/Density/*` plus the vendored `ZInQKernel/Sieve/*`:

| File | Content | Lines |
| --- | --- | --- |
| `CharSum` | point count, scaling, Jacobsthal, divisibility by 4 | 300–450 |
| `Description` | `InClass`, `cp`, `goodSlopePrime_of_gcd` | 200–300 |
| `Abel` | Dirichlet density ⇒ `PrimesRelUpperDensityPos` | 250–400 |
| `Residues` | CRT count of `A_L`, main term via `LSeries_residueClass_lower_bound` | 250–400 |
| `PrimeTail` | `Σ_{ℓ>L} ℓ^{−2} ≤ 4 log 4/(L log L)` | 100–200 |
| `Lattice` | the count for `ℓ > N^{1/4}` | 200–300 |
| `Sieve/*` | port of PrimeNumberTheoremAnd `v4.34.0` | 1536 existing |
| `GaussSieve` | Lemmas 4.3–4.5, `uniformBadBound` | 900–1500 |
| `PropD` | `goodPrimeDensity_of_uniformBadBound`, `goodPrimeDensity` | 150–250 |

The milestones are:

1. `goodSlopePrime_of_gcd`.
2. `goodPrimeDensity_of_uniformBadBound`. This reduces Proposition D to one explicit counting statement
   about integers.
3. The sieve port.
4. `uniformBadBound`. Then `GreenTaoDense → GoodPrimeAP` follows via `gt-search`'s
   `progressions_above_of_greenTaoDense`.

**First step:** `jacobsthal`, `four_dvd_pointCount` and `goodSlopePrime_of_gcd`. Success means they
build with standard axioms and reprove `GoodSlopePrime 17` (`cp 17 = −1`).

## Ranking

1. DS-cond (files 1–6 and 9; Proposition D modulo `UniformBadBound`): high chance.
2. DS (adds the sieve port and the instance): high chance, larger volume.
3. Natural density through `WeakPNT_AP`: medium; it depends on PrimeNumberTheoremAnd's `sorry`s.
4. Hecke, for the exact constant: low chance, and the constant is not needed.
5. A sieve-free `G*`: low chance; §4.6 says no.

## Open questions

- PrimeNumberTheoremAnd was found only at tag `v4.34.0`. Port effort to Mathlib `56a00585` is unknown.
- Would a cheaper upper-bound sieve (non-optimal Λ² weights) be shorter in Lean than porting Selberg's?
- The other half of the trust base: does any formal Green–Tao proof cover dense subsets (Theorem 1.2)?
  See `gt-search.md`.

## Suggested follow-up tasks

1. **pd-lean-1**: files 1 and 2 (the first step, §6.5). Success criterion as above.
2. **pd-lean-2**: files 3–6 and 9-conditional, giving `goodPrimeDensity_of_uniformBadBound`. Then add
   `GoodPrimeAP` from `GreenTaoDense` plus `UniformBadBound` as a theorem.
3. **pd-sieve-port**: port the PrimeNumberTheoremAnd `Sieve/*` files to the pinned Mathlib, and
   instantiate `BoundingSieve` for the box of §4.3 at `ℓ = 5`.
4. **rv-pd-paper**: an independent referee report on §4.3–4.5 (the constants, and the match with
   `selberg_bound_simple`'s hypotheses).
