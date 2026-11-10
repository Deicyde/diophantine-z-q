# nt-22p report: making the prime-pattern hypothesis cheaper

Full note: `docs/research/nt-22p.md`. Marks: VERIFIED / STANDARD / SPECULATIVE / UNCHECKED as there.

## Summary

1. **Density of good slope primes (Q1).** The set `G` of good slope primes has positive natural
   density unconditionally: about 0.106 of all primes. It matches the Euler product
   `(1/8)∏_{ℓ≡1(4)}(1 − 2/(ℓ−1)²)`; computed on all primes up to 3·10⁶ (VERIFIED). The infinite family
   of conditions behind `gcd(d₁, d₂) = 4` is cheap because `E` has CM by `ℤ[i]`. An odd `ℓ` divides
   both orders iff `ℓ | a` and `ℓ | p + 1`, where `p = a² + b²`. That has density `≍ 1/ℓ²`, so small
   `ℓ` are removed by congruences and large `ℓ` by a lattice sieve. This is the manuscript's own
   argument (lines 1554–1642, record A072, with the order of choices at 1682–1704). It needs no GRH,
   and I found no gap: **no defect in the manuscript**.

   The full gcd condition is used only in `Mult.shift_choice` via `exists_shift`, and there an
   odd-part condition at every `ℓ ∤ c_*` is necessary for the honest witnesses to exist. So no
   finite Chebotarev version serves the present test. With item 2 this does not matter, since only
   positive density is used.
2. **Green–Tao 2008 suffices (Q2), via a change in the completeness proof.** Obstacle R4 of
   rs-pattern was control of the common difference at the old primes. It disappears once the free
   witness `q` of the slope predicate (`a = 1 − R₀q²`) is used. Suppose a slope has a pole of order
   `e` at an old prime `ℓ`, with `F(t) > 0` (and `e ≥ 3` if `ℓ = 2`). Then `R₀` is a square in `ℚ_ℓ`,
   and choosing `q` near `R₀^{−1/2}` ℓ-adically makes `v_ℓ(B) ≥ 4` (**Lemma P**, §3.2; checked by
   hand and on 30 samples). Lemma P is needed only at `S₀ = {2,3,5,7,13}`: elsewhere the
   pole-completeness hypothesis asks only for parity, which is automatic.

   With this change the slope representation follows from **22P_AP: the good primes above `max S_b`
   contain arithmetic progressions of every length** (Proposition AP, §3.3). The pattern uses the
   fourteen points `𝒞 ∪ {1} ∪ (A+10−𝒞) ∪ {A+9}` with the constant slope −10, and the sign condition
   `F(t) > 0` holds automatically for both variable slopes.

   22P_AP is a direct corollary of Green–Tao 2008, Theorem 1.2 (Szemerédi in the primes; statement
   checked against the arXiv TeX source) and of the density result. The GTZ inverse theorem, the
   Möbius–nilsequence theorem, the linear-equations asymptotic (record A021), the singular-series
   analysis, the uniform two-variable Selberg sieve and the fibre count all leave the trust base of
   this hypothesis. The polynomial is unchanged.

   No theorem in the literature with valuation-restricted common differences was found, and none can
   hold in general. After Lemma P none is needed.
3. **Fewer forms (Q3): no.** Within constructions that are linear in the parameters:
   - each slope of large height needs all six contact forms prime, a system of true complexity 4,
     which is beyond the circle method. Square-like values lead to curves of positive genus or to
     binary quartics.
   - one variable slope plus constants fails on a positive density of `A`: by Faltings there are
     only finitely many smooth slopes, and a Chinese remainder argument finishes it. Numerically,
     though, constant combinations cover all `|A| < 3000`.
   - two cooperating slopes and one constant are therefore the minimum. Their forms lie in one
     arithmetic progression, which is exactly the shape Green–Tao 2008 handles.
   - the contact set has a dihedral Möbius symmetry group of order 12, of no use for the pattern.

## Ranking

| Rank | Route | Payoff | Obstacle | First test / success criterion | Chance |
| --- | --- | --- | --- | --- | --- |
| 1 | AP: Lemma P + field 2′ + `GoodPrimeAP` | 22P becomes "good primes contain arbitrarily long APs", a corollary of GT08 | Lean: field 2′ of `GoodSlope`, Hensel square root, residue-target `weak_approx_q` | prove the integer form of Lemma P(1)–(2), then `slopeRepresentation_of_goodPrimeAP`; success = main theorem builds with `GoodPrimeAP` | high |
| 2 | D: write out the density of `G` | GT08 plus textbook inputs justify 22P_AP | uniform lattice sieve, CM identification for primes `p` | explicit-constant proof; the predicted lower bound at `L = 50` is positive and below 0.1064 | high |
| 3 | R: `gcd(d₁,d₂) ∣ c_*` | cleaner `GoodSlopePrime`, density 0.85→0.88 | none | `exists_shift` builds with the weaker hypothesis | high, low value |
| 4 | F: finitely many Chebotarev conditions | `G` a Chebotarev set | impossible for the fixed-shift test | a test whose success at `p` is a Frobenius condition in one fixed field | low |
| 5 | C: ≤ 3 simultaneous prime forms | Fourier-analytic proof | true complexity 4 per slope | none sensible | negligible |

## Open questions

- Lemma P and Proposition AP are checked by hand but not in Lean. The interaction with the Lean proof
  of `slope_complete` (which consumes `GoodSlope.old` through `old_le_Cp`) must be rechecked when
  field 2′ is introduced.
- Proposition D is a transposition of the manuscript's sieve, not yet written out with constants.
- The attribution of the CM cyclicity results (R. Murty 1983, Cojocaru 2003) is from memory
  (UNCHECKED). The argument does not depend on them.
- Is Green–Tao 2008 the floor? Inside this architecture, yes: arbitrarily long patterns of true
  complexity ≥ 4 in a dense subset of the primes are needed. Formalizing GT08 (with Szemerédi's
  theorem) remains far beyond the project.

## Suggested follow-up tasks

1. **ap-lean**: in Lean, add `GoodPrimeAP`, field 2′, the local square-root lemma and the modified
   `weak_approx_q`; prove `slopeRepresentation_of_goodPrimeAP`; rewire `Main.lean`.
2. **ap-density**: write Proposition D in full, with explicit constants, as a note or manuscript
   appendix, and check it numerically.
3. **ap-manuscript**: draft a replacement for Proposition 6.2 and its proof: the progression form,
   Lemma P in the completeness paragraph (lines 1735–1758), and a citation of GT08.
