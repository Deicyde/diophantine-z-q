# pc-audit: audit of the deep inputs of Route K for pole completeness

Deliverable: `docs/research/pc-audit.md`. Scripts and outputs: `scratch/pc-audit/`. The branch
also merges `wip/rs-pole` and `wip/rv-route-k`.

## Summary

Route K moves the pole polynomial to congruent number curves `C_d : y² = x³ − d²x` and replaces
the manuscript's restricted converse RC (Theorem 5.3, about 8,000 lines and 39 audit records) by
a 2-converse for `C_d`. Read against the sources (arXiv LaTeX and PDF of Kriz v5, TYZ v1 and
Smith v2), the deep input Route K needs is only:

> **rank `C_d(ℚ) ≥ 1`, for at most two Selmer-minimal curves per input, chosen by the
> descent.**

A point with the prescribed first Kummer coordinate `β` then follows by counting: rank ≥ 1 and
`dim Sel₂ = 3` force `C(ℚ)/2C(ℚ) = Sel₂` (RK9). Neither Cassels–Tate, Poonen–Stoll nor
finiteness of Ш is needed at this step.

## Verdicts per input

- **Kriz, Theorem 10.13** (arXiv:2002.04767v5, 2022): usable with an extra hypothesis.
  - It is an unrefereed preprint (no journal reference on arXiv or Crossref).
  - It covers every converse curve, with no congruence condition.
  - The LMFDB cases `f₀ ≤ 3` are never needed: they are `|d| ∈ {1, 2, 3, 6}`; `C_1`, `C_2`,
    `C_3` are not Selmer-minimal and `C_6` has the point `(−3, 9)`. The converse curves can be
    taken with `f₀ ≥ 11`.
  - **New finding:** the proof of Theorem 10.8, on which 10.13 rests, refutes its contradiction
    hypothesis with `E' = 256b1`. That curve has `f₀ = 1`, violating the proof's own
    assumption `f₀' ≥ 4`. The step is repaired by `C_5` (conductor 800, `f₀ = 5`, rank 1,
    `r₂ = 1`, analytic rank 1; checked with PARI).
  - Theorem 9.23 (rank zero) is not needed.
- **Tian–Yuan–Zhang, Theorem 1.2** (Asian J. Math. 21 (2017) 721–774; read in arXiv v1): usable
  with an extra hypothesis.
  - It is published, but certifies analytic rank one only for part of the Selmer-minimal `C_d`:
    in samples 88%, 60% and 93% for `|d| ≡ 5, 6, 7 (mod 8)`; asymptotically 3/4, 1/2 and 3/4.
  - Its §1 statement is ambiguous about the factor `d₁`. The end of the proof of Theorem 3.5
    fixes the reading that agrees with Smith.
  - The journal text could not be retrieved; it must be compared with arXiv v1.
- **Smith, Theorem 2.2** (arXiv:1603.08479v2, unrefereed): usable.
  - Independent check of TYZ's genus sums, with class groups from PARI, against Smith's bordered
    determinants: 0 mismatches over all 12,159 squarefree `n < 20000` and 450 random `n` with
    4–9 primes.
  - The proof is complete but terse.
  - One prose slip: the definition of `g` is stated backwards; Table 1 is correct.
- **Gross–Zagier** (part of A020): only "analytic rank 1 ⟹ rank ≥ 1" is needed. BCDT and
  Kolyvagin are not needed, because `C_d` is CM, hence modular classically.
- **Cassels–Tate** (A019): needed only in the Kriz variant, to get corank 1 from
  `dim Sel₂ = 3`.

## Main new observation (RK6)

For a Selmer-minimal `C_n`, TYZ's criterion is a linear functional evaluated on the non-torsion
Selmer class:

- a proved bordered-determinant lemma;
- the kernel of Smith's block equals `(S(x+n), S(x))` for `n ≡ 5` and `(S(x+n), S(x−n))` for
  `n ≡ 6` (300 of 300 each);
- explicit rules checked on 900 curves.

For `|n| ≡ 5` (row 5b) and `|n| ≡ 6` (row 6) the rule depends only on the first coordinate `β`.
Since `θ ≡ 1 (mod 8)`, it holds for `C_n` and `C_{nθ}` simultaneously. So the TYZ route costs
only a 2-adic choice of the multiplier (16 or 32 of 64) and a congruence on `n' mod 8`.

Tests of the `β`-rules:

- 1,348 rule predictions against determinants on Route K solutions: 0 violations.
- Descent search restricted to the `β`-rules (K-TYZ-β): KTYZB_SUMMARY

## Ranking

1. **K-TYZ-β** (TYZ + two rows of Smith + Gross–Zagier, with a 2-adically restricted descent):
   recommended. Chance medium.
2. K-Kriz: mathematically simplest, but the citation is an unrefereed preprint.
3. K-L: a narrow Lean hypothesis in the form consumed, after 1 or 2.
4. K-TYZ with all rows: fallback for searches only.

## Open questions

- The Route K descent lemma is still unproved, in both forms. The K-TYZ-β form additionally
  prescribes `n' mod 8` and restricts `m`.
- Written proof of the kernel identification in RK6, by matching Smith's symmetrized matrix with
  Monsky's parametrization of `Sel₂`.
- Compare TYZ's journal statement with arXiv v1.
- Kriz: publication status, and an author confirmation of the repaired Theorem 10.8.

## Suggested follow-up tasks

1. **descent-ktyz**: prove the descent lemma in the K-TYZ-β form. Validate the algorithm it
   defines on 30 inputs of each `rv-route-k` generator, with `sel2cong.py` and Smith's row 5b/6
   determinant. Start from `scratch/pc-audit/ktyz_beta_search.py`.
2. **smith-rows**: write self-contained proofs of Smith's rows 5b and 6 and of the RK6 kernel
   identification (pure 𝔽₂ linear algebra).
3. **tyz-journal**: obtain the Asian J. Math. text and confirm Theorem 1.2's statement and
   numbering.
