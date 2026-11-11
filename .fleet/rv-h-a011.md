# rv-h-a011: review of the audit record A011-V14 (`docs/research/h-a011.md`)

**Verdict: proved after the listed repairs.**

No mathematical gap. Every hypothesis of Pan's Theorem 1.0.4 (arXiv:1901.07166v2) is
discharged:

- for the right representation, `r₅` of `G_ℚ`, with checks on `G_F` or on `G_{K'}` only where
  the property passes to `G_ℚ` or to `G_{ℚ₅}`;
- at `p = 5`;
- over the right local field, `K' = F_w(A[3]) ⊇ F_w`.

This holds relative to the sources that could not be read here. The repairs fix overstated
evidence, descriptions and wording. No argument and no constant of Theorem 4.1 changes.

**Deliverables.** The review note `docs/research/rv-h-a011.md`. The log and one script are in
`scratch/rv-h-a011/`. No Lean was run: this is a paper-side review.

## Findings (severity; none is a gap)

1. **F1, moderate.** The record cites V14's bibliography (L23910-23913) as evidence that the JAMS
   text numbers the theorem 1.0.4. That entry cites arXiv v2 explicitly ("the historical
   author-proof version"), so the evidence is circular. The record's proposed manuscript text
   and leaf wording cite "[Pan, JAMS 35 (2022), Theorem 1.0.4]", a numbering that is UNCHECKED.
   - *Repair R1:* cite "arXiv:1901.07166v2, Theorem 1.0.4, published in JAMS 35 (2022)".
   - The other evidence was rechecked and holds: the v2 date 2021-09-03 with the comment
     "revised version"; Crossref's metadata and abstract.
   - The AMS text could not be read here either.
2. **F2, minor.** §1.2, marked VERIFIED, misdescribes Pan's Theorem 8.0.1. It also requires
   `ρ|G_{ℚ_p}` absolutely irreducible, that is, the non-ordinary case.
   - The ordinary cases rest on Skinner–Wiles 1999/2001, and one subcase on Kisin and Hu–Tan
     (Remarks 8.0.3 and 9.0.2; intro L224 "combining").
   - So Pan's paper does not prove every case of 1.0.4 itself.
   - *Repair R2:* correct the description, and state the policy explicitly: cited works inside a
     refereed theorem's proof are not leaves. V14 L673-675 uses the same policy.
3. **F3, minor.** "Hidden Berger dependency removed" holds only at the interface. Pan's body
   theorems assume "de Rham", and pst ⇒ dR is elementary. Whether Pan's proof uses dR ⇒ pst
   internally was not examined. Route (c)'s Berger in turn rests on André's theorem.
   - *Repair R3:* reword as "removed from the hypothesis check".
4. **F4, minor.** Breuil's Corollaire 5.3.4 is quoted exactly and applies:
   - `p ≠ 2`;
   - finite residue field, which the proof of Lemme 5.2.1 covers explicitly;
   - `K` totally ramified over `W(k)[1/p]`.

   But the direction used, reduction ⇒ representation, is only attributed to Fontaine, with no
   reference. Two points in the record need correcting:
   - Coleman–Iovita's p. 3 sentence has "if" and "only if" swapped, so the record's reading of
     it is an interpretation.
   - Their arXiv file has no bibliography, so "[Fo-BT] = Ann. Math. 115 (1982)" was not read.

   *Repair R4:* put that caveat next to "STANDARD" in the Summary and in §7.
5. **F5, informational (SPECULATIVE).** The record says Scholze must stay. But V14's twist and
   weight argument needs only "de Rham with weights `{0, −1}`", not the filtered comparison.
   Under route (a) (good reduction over `K'`), Tate's 1967 Hodge–Tate decomposition, which is
   UNCHECKED, plus the determinant check might remove Scholze and the erratum. This is a
   possible follow-up.
6. **F6, minor.** The proposed manuscript edit leaves two other V14 citations of the survey and
   the supplement for the same lemma: L10386-10389, and the "Height" row of the applications
   table at L13296-13300.
   - *Repair R5:* list them.
   - The trust-leaf delta for H is unaffected: inside V14 §4, `direct-p5` is cited only at L680,
     and the four remaining supplements are exactly `a001`, `ly-d6`, `b11` and `igusa-theta`
     (VERIFIED by grep).
7. **F7-F9, informational or trivial.**
   - V14 fixes only `C ↪ Q̄₅`, so the choice of `Q̄ ↪ Q̄₅` and of `g` up to conjugation needs a
     sentence. Both choices are harmless.
   - "exactly the application at L1501-1503" uses a different base field, with the same
     criterion.
   - The polarization line is L636-637, not L634-636.

## What was verified

- **Pan's statement.** Conjecture 1.0.1 and Theorem 1.0.4 are quoted exactly (FM.tex L167-177,
  L226-233). There is no residual hypothesis at `p ≥ 5`.
- **Conventions.** `ε` has HT weight `−1`, as in V14 L537; `Frob` is geometric (FM.tex L268,
  L270).
- **The interface with V14 L561-666** is insensitive to the Frobenius convention. The argument
  is `U^∨ ≅ U ⊗ det^{−1}` in dimension 2, plus Chebotarev.
- **The discharges** H1-H7 are correct for the right group, prime and field.
- **The summand lemma** is correct: `D_st` is additive, `V₅(A) ⊗ E ≅ V₅(A)^{[E:ℚ₅]} ≅ r₅ ⊕ r₅`
  on `G_{K'}`, and `dim D(r₅) = dim r₅`.
- **The determinant check** is correct: `(det r₅)² = det V₅(A) = ε₅²` on `G_F`, so
  `a + b = −1`, which forces `a ≠ b`.
- **Route (a).** `(2, −3)` is ramified exactly at `{2, 3}` (`hilbert_check.py`), so Lemma PG
  works at 5 with `V₃`.
- **Route (c).** Berger v3, Théorème 0.6 = Théorème 5.19, is as quoted.
- **Constants.** No constant of `H₆(S;R)` changes: the lemma is qualitative and `K'` enters no
  bound.

## Still UNCHECKED (could not be read here)

- Pan's JAMS text.
- Silverberg–Zarhin 1995, Theorems 3.3 and 3.5. Their own 1997 paper cites Raynaud's criterion
  as SGA 7 IX Prop. 4.7.
- The Fontaine sources for the direction of Breuil's corollary that is used.
- Berger's *Inventiones* numbering.
- Faltings 1986, Serre–Tate, Milne 1986 and 2005, Fontaine 1994, Scholze's journal version and
  erratum, Deligne–Serre, Kato, Washington, Shimura and Li.
- Tate 1967 (F5 only).
