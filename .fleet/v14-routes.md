# v14-routes report: does Version 14 have a new proof route?

Deliverable: `docs/research/v14-routes.md`. Scripts, diffs and log: `scratch/v14-routes/`.

## Summary

**No.** Version 14 changes none of the inputs behind our four hypotheses. Its new section builds a
smaller quartic for the second ("quartic") construction, keeps every arithmetic input of Version 13,
and states that the main polynomial is unchanged.

- **What could be read.** `~/gt-src/v14/quartic_v14.tex` is a 127-byte GitHub "Not Found" reply,
  not TeX, and the upstream repository could not be fetched from this machine. I compared:
  - the 11/5 manuscript against Version 13 (full source, November 7), by diff;
  - Version 13 against `addition.tex`, the new Version 14 section `sec:v14` (955 lines, "A quartic
    presentation with 299 variables").

  Any Version 14 change outside that section has not been seen.
- **Version 14 section** (VERIFIED).
  - Theorem `thm:v14-quartic`: quartics `P_299` (6,630 monomials) and `P_314` (coefficients below
    `2^6496`) whose rational zero projection is ℤ.
  - Its text: "We retain the arithmetic inputs, qualifications and source editions of Sections
    v12-inputs and v13. The polynomial of the main construction is unchanged" (V14 L5-7).
  - The changes are private-witness changes with inverses, plus re-certified test groups, a
    parity anchor and a weak-approximation completeness argument.
  - Phrases like "fixed-difference chart for H" and "H-depth bootstrap" refer to an auxiliary
    point named `H`, not to the height hypothesis.
- **11/5 against Version 13, main construction** (VERIFIED).
  - These statements are byte-identical: Theorem 4.1 (`thm:height`, N5 404 / V13 480), Lemma 5.1
    (988/1067), Theorem 5.2 PC (1001/1080), Theorem 5.3 RC (1005/1090), Lemmas 5.4-5.5
    (1072/1157, 1086/1171) and Proposition 6.2 (1267/1385).
  - What changed:
    - attributions to OpenAI's preprints;
    - an explicit statement of the conjugation in the multiplication tests, which our Lean template
      already applies;
    - a fuller valuation deduction in §6;
    - three repairs inside the proof of RC: Kato 1999 Theorem 0.8 at the prime 2 (§7, Appendix E),
      the off-filter scope in §8, and a determinant-specialization lemma in §9.
  - Appendix F is unchanged; Appendix G changes only the layout of one display.
- **The quartic route** (Version 13 sections 14-18 and appendices I-L, and Version 14). It is a
  different construction on the same curve: an isomorphic model of our `E`, with `P_*` the image
  of `P₀` (checked exactly in `checks.py`). It uses:
  - a five-contact height estimate (`thm:quartic-height19`, exponent 19, `log₂ H_19 < 2093966`),
    proved like Theorem 4.1: Shimura curve of discriminant 210, QM surfaces, Pan's modularity,
    Faltings heights, isogeny estimates;
  - a seven-witness pole predicate (`hyp:o8-pole`) proved from the same RC for the `x + 3ℓ`
    curves;
  - a simultaneous Gaussian-prime theorem (`thm:v5-simultaneous-primes`, after Sun,
    arXiv:2610.20691), proved in a 2,600-line nilsequence appendix.

## Changes that matter

- **To our hypotheses: none.**
  - **SixContactMin:** Theorem 4.1 is unchanged. The quartic route's estimate is equally deep and
    concerns another contact set.
  - **CertifiedRankSel:** Route K uses neither RC nor its proof, so the repairs in §§7-9 and
    Appendix E do not touch it. Lemma 5.5 (GZK) is unchanged and still cites Kolyvagin's MPIM
    preprint.
  - **GreenTaoDense and GoodPrimeDensity:** Proposition 6.2 is unchanged, and the quartic route's
    prime theorem is strictly harder.
  - **Switching our Lean development to the quartic route** would be legal, since the frozen
    target accepts any polynomial within its bounds. It would take months of new soundness and
    completeness proofs and remove no hypothesis (SPECULATIVE estimate).
- **Two pointers.**
  - Version 13 calls RC "the `E = E_ℓ`, `s₂(E) = 1` case" of OpenAI's *pointwise 2-converse for
    elliptic curves with rational two-torsion* (7 Oct 2026). If that theorem covers the curves
    `C_d`, it is a second, independent (unrefereed) source for CR₃^Sel. It could not be read here
    (UNCHECKED).
  - The exponent-19 height proof is a new transfer argument: `X_H` with the nebentypus kernel and
    Gaudron–Rémond 2023 Theorem 1.9(1), instead of `J₁(N)` and GR 2014. It gives a constant
    polynomial in the radical, but uses the same classes of deep input. GR 2023 is not on arXiv.

## Recommendation

1. **Keep GoodPrimeDensity and GreenTaoDense first.** They are the only hypotheses that Lean work
   can remove, and both are in progress. Version 14 confirms there is no cheaper prime input.
2. **Next new attack: CertifiedRankSel, elementary half into Lean.** Proposition 0 is now a Lean
   theorem. The next unrefereed new mathematics in CR₃^Sel's justification is therefore the 𝔽₂
   step of tyz-5b §4 (Lemma 4.1, Lemma 4.2, Theorem 4.3), from "8 Selmer solutions, one with
   `|a| ≡ 7 (mod 8)`" to `det M_5b = 1`.
   - *First task:* define `M₁` and `M_5b` over `ZMod 2` from the Route K Legendre data and prove
     Theorem 4.3 against the Lean system. Then state `CertifiedRank5b` (8 Selmer elements and
     `det M_5b = 1` imply that every Selmer class is a point) and derive `CertifiedRankSel` from it.
   - *Success:* `lake build` and `check_target.py` pass, and Theorem 4.3 is proved for all `r`
     with the standard axioms only. A `decide +kernel` cross-check for `r ≤ 4` matches brute-force
     counts.
   - *Chance:* high. *Payoff:* medium. The follow-up is tyz-5b §3 (`det M_5b = T_5b`, forest
     lemma), which leaves only TYZ, Rédei and GZK as trusted.
3. **SixContactMin** has no elementary half. Version 14 adds nothing for it. The paper-side
   steps of nt-h §5 (Serre route, NoCM) remain the next steps.

No manuscript, blueprint, Lean file or other note was edited. All work is committed on
`wip/v14-routes`.
