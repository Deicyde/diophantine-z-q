# rv-nt22p-ap report: referee of nt-22p (Proposition AP, Proposition D, the Green–Tao step)

Full report: `docs/research/rv-nt22p-ap.md`. Scope: nt-22p §2, §3.3, §3.4. Lemma P(2)–(3) and the
modified slope completeness of §3.2 were outside my scope and are taken as given (other referees).

## Verdict

- **Proposition AP: proved as written**, given §3.2 (field 2′ in place of field 2 in slope
  completeness). Every step checked: the set `S_A⁺` and the indexing, lowest terms, field 1, the
  signs `F(t₁), F(t₂) > 0` for every integer `A` (including the switch `A′ = −59/−60`), field 2′
  with Lemma P(1), fields 3 and 4 (the argument of `goodSlope_of_primeValues` carries over with
  the hypothesis `hold` dropped), and the constant slope −10.
- **Proposition D: correct as a sketch.** The CM description of `GoodSlopePrime` holds for
  `p > 324` (checked by hand and by computation against the literal Lean definition). The density
  `(1/8)∏(1 − 2/(ℓ−1)²) ≈ 0.106` is a relative density among the primes, as Green–Tao needs. The
  sieve is the manuscript's own, transposed; it still has to be written out.
- **Green–Tao step: correct.** Checked against the TeX source of arXiv math/0404188v6:
  Theorem 1.2 needs positive *relative upper* density; its progressions are non-degenerate
  (`r = 0` is discarded) genuine progressions of primes, so `x ≥ 1`, `v ≥ 1`, and `x > N` once it is
  applied to `G ∩ (N, ∞)`.
- **Trust base: the claim is right in substance** (GTZ + MN + linear equations replaced by
  Green–Tao 2008), with the qualifications F3–F5 below.

No critical or major findings.

## Findings (severity)

- **F1 (minor).** `K_A ≈ |A| + 71` is wrong: `K_A = A + 130` for `A ≥ −69` and `K_A = −A − 8` for
  `A ≤ −70` (minimum 61). Harmless. Consequence: `8 | v` always, so Lemma P's delicate case `ℓ = 2`,
  `e ≤ 2` never arises.
- **F2 (minor).** "Fourteen numbers" should be "at most fourteen": `T` and `A′ − T` can meet.
  Shared primes between `t₁` and `t₂` are harmless.
- **F3 (minor, trust base).** Green–Tao 2008 prove Theorem 1.2 only in outline (§10: "we leave the
  details to the reader"). The Conlon–Fox–Zhao exposition proves only Theorem 1.1. Cite a complete
  proof of the dense-subset form. The labels in §3.1 (UNCHECKED) and §3.4 (VERIFIED) disagree; the
  number 1.2 is correct.
- **F4 (moderate, trust base).** Lemma P, the modified choice of `q` and Proposition AP are not
  formalized. Today `SlopeRepresentation` is kernel-checked from 22P₂, so for the Lean main
  theorem the trust base shrinks only after the Route 1 work: field 2′, a new `part1` of
  `pole_input_valuations` (the only consumer of field `old`), and a residue-class weak
  approximation. The table should mark those rows "to be formalized".
- **F5 (minor).** In the write-up of Proposition D, cite the uniform two-dimensional sieve for
  `L < ℓ ≤ N^{1/8}` (manuscript `eq:prime-selberg`, or Brun–Titchmarsh in `ℤ[i]`); trivial
  counting does not suffice. Also keep the term `√N log N` in the tail.
- **F6 (minor).** Green–Tao 2008 need Szemerédi's theorem in finitary form *without* quantitative
  bounds, not "in its quantitative finite form".

## Computations (own scripts, scratch/rv-nt22p-ap/)

- Literal `GoodSlopePrime` vs CM description: 0 mismatches for all `325 ≤ p ≤ 2·10⁵` (brute-force
  point counts up to 40000, PARI `ellcard` beyond); 1,925 good primes below `2·10⁵`.
- Good share of primes up to `3·10⁷`: 0.10610; Euler product × 1/8: 0.10602.
- Proposition AP algebra: 149 values of `A`, synthetic progressions with `v_ℓ(v)` up to 30 at
  `S₀`. Signs, field 1, valuations and indexing hold in every case; `R₀` is a square in `ℚ_ℓ` in all
  7,778 Lemma P cases.

## Suggestions

1. Adopt 22P_AP as stated, in the Lean form `∀ K N, ∃ x v, N < x ∧ 0 < v ∧ ∀ j ≤ K,
   GoodSlopePrime (x + j v)`; it is a direct special case of Green–Tao 2008, Theorem 1.2, given
   Proposition D.
2. Do not record the hypothesis as replaced until the Route 1 Lean work builds and the other two
   referees clear Lemma P and the modified slope completeness, which carry the real new mathematics.
3. Write out Proposition D with the manuscript's sieve (Route 2), and fix F1, F3, F6 in the note.
