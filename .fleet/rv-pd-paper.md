# rv-pd-paper: referee report on pd-paper.md (Proposition D in full)

Deliverable: `docs/research/rv-pd-paper.md`. Log: `scratch/rv-pd-paper/log.md`. Scripts:
`scratch/rv-pd-paper/{sec1,sec4}.py` (output `sec4.out`). Lean checks:
`scratch/rv-pd-paper/pntsieve/src/{Check,Instance}.lean`.

## Verdict

**Proved as written.** Theorem D (positive lower Dirichlet density of `G*_L ⊆ G`) and Proposition 5.3
(Dirichlet density implies `PrimesRelUpperDensityPos`) are correct. So `ZInQ.GoodPrimeDensity` holds on
paper. I checked every step of §§1–5 myself. I found no mathematical gap, and every explicit constant is
right: `A₁ = 16003`, `N₁ = e^{1920}`, `log L ≥ 15A₁ = 240045`, `δ_L ≥ 3/(8(L − 1))` and
`α_L < 5.55A₁/(L log L)`.

## What was checked

- **§1 (character sums against the literal `GoodSlopePrime`).** The scaling identity, the involution
  `x ↦ −D²/x` giving `4 ∣ #E`, Jacobsthal's identity, the gcd formula `4·gcd(c_p, p + 1)` and
  `bad ℓ ≡ 1 (mod 4)` are all correct. An independent recomputation for all class primes `p < 3·10⁴`
  (806 pairs `(p, r)`) found no failure. The literal predicate agrees with the prediction for every odd
  prime below `3·10⁴`.
- **§§2–3.** The conditions are congruences modulo `M_L`, together with `p ≡ 1 (mod 8)` and
  `(p/7) = −1`, i.e. conditions in `ℚ(ζ₈, √7)`. Mathlib's `LSeries_residueClass_lower_bound`
  (`PrimesInAP.lean:348`) has exactly the quoted statement, and Lemma 3.1 follows.
- **§4 (main weight).** The sieve data match every field of Mathlib's `BoundingSieve` and `SelbergSieve`.
  `selberg_bound_simple` has exactly the quoted statement and no further hypotheses. The local density
  `ν(q) = (2q − 1)/q²`, the remainder bound, the error term at level `N^{1/20}`, Lemma 4.5 with Claims A
  and B, the constants of Proposition 4.2 and the lattice count of Proposition 4.1 are all correct. Each
  was also tested numerically, and every inequality held with margin.
- **Lean.** PrimeNumberTheoremAnd tag `v4.35.0` pins our Mathlib `56a00585`. Its sieve files
  (`AuxResults`, `Basic`, `Selberg`) compile unmodified against our tree, and `selberg_bound_simple`
  depends only on `propext`, `Classical.choice` and `Quot.sound`. The §4.3 data build as a
  `SelbergSieve` with every field proved, and the theorem applies verbatim.
- **§5.** Lemma 5.1, the Abel summation of Lemma 5.2, Proposition 5.3 (Mathlib
  `eventually_primeCounting_le`) and the assembly of Theorem D are correct.

## Findings (all minor or cosmetic)

1. **F1 (minor, Lean plan).** `sum_quadraticChar_shift_mul` is false for `p = 2`. Add `p ≠ 2`.
2. **F2 (minor).** PrimeNumberTheoremAnd has a `v4.35.0` tag on our exact Mathlib. File 7 is a verbatim
   vendoring of 1007 lines, not a port of 1536. This answers open question 1 and removes the version
   obstacle of Route 2.
3. **F3 (minor).** The target is now `ZInQ.GoodPrimeDensity` in `ZInQKernel/Hypotheses/GreenTao.lean`
   (main), which already proves `goodPrimeAP_of_greenTaoDense`. The `GTSearch` scratch link is
   superseded.
4. **F4 (minor, unused remark §4.6).** Brun's pure sieve reaches `z = exp(c log N/log log N)`, not
   `(log N)^{O(1)}`. The conclusion that it is insufficient stands.
5. **F5, F6 (cosmetic).** Lemma 3.1 in Lean needs a comparison from exponent 1 to exponent `x`, because
   `summable_residueClass_non_primes_div` is at exponent 1. One file path in §4.4 is incomplete.

## Suggestions

- If `w = ⌊N^{1/40}⌋₊` is used in Lean, raise `N₁` to about `e^{2400}`, or keep the prime filter real.
  The constants have ample slack (the empirical constant is `≤ 0.42` against `A₁ = 16003`).
- Prove Lemma 4.4 as a general box-in-residue-set count, then specialise.
- Keep `UniformBadBound` as the intermediate milestone. Every ingredient of
  `goodPrimeDensity_of_uniformBadBound` is checked above.
