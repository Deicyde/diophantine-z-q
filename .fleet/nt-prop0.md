# nt-prop0: scoping a Lean proof of Proposition 0 (`Σ(𝒞_d) = Sel₂(C_d)`)

The deliverable is `docs/research/nt-prop0.md`. Scripts and two Lean probes are in
`scratch/nt-prop0/`.

## Summary

- **Definition of `Sel₂`, statable in Lean.**
  - `Sel₂(d)` is the set of pairs of squarefree integers `(a, b)` whose 2-covering
    `D_{a,b} : a z₁² − b z₂² = d w², a z₁² − ab z₃² = −d w²` has points over `ℝ` and over every `ℚ_p`.
    Lean states it with the "x-form" `Loc K d a b`: `a, b` are squares, or some `x` has
    `x/a, (x − d)/b, (x + d)/(ab)` all squares. Only `ℚ_[p]`, `ℝ` and `IsSquare` are needed.
  - Lemma 1.2 (proved, over any field of characteristic ≠ 2, with no group law): the covering has a
    `K`-point iff `(a, b)` is in the image of the explicit Kummer map. With Silverman X.1.4, this is the
    textbook Selmer group.
- **The hypothesis in the literature's form.** With Proposition 0 in Lean, CR₃ follows from:
  > `CR₃^Sel`: if `d ≡ 5 (mod 8)` is squarefree, `#Sel₂(d) = 8`, and `Sel₂(d)` contains a pair with
  > `|a| ≡ 7 (mod 8)`, then every element of `Sel₂(d)` has a rational point on its covering.

  - Given X.1.4, this is equivalent to `rank C_d(ℚ) ≥ 1` for these `d`, i.e. `Ш[2] = 0`.
  - The derivation of `CertifiedRank` from `CR₃^Sel` plus Proposition 0 is written out (§1.4) and is
    elementary.
- **Local computations, all written in the order Lean needs (§2).**
  - Square classes of `ℚ_p` via Hensel.
  - Real place: a sign argument.
  - Odd `p | d`: a case analysis on `v_p(x)`, whose image is the span of the torsion images.
  - `2`, for `d ≡ 5 (mod 8)`: eight explicit rational witnesses (`x = 1/4`, `−4d²`,
    `d(1+4d)/(1−4d)`, `−d(1−4d)/(1+4d)` and the torsion points), plus a case analysis on `v₂(x)` mod 8.
  - Good primes `p ∤ 2d`:
    - necessity uses valuations only;
    - sufficiency is new here and needs **neither the group law nor the Hasse bound**. It combines a
      character-sum count over `𝔽_p`, Jacobsthal's identity `Σ_n S(n)² = p(p−1)(1+χ(−1))` (elementary,
      gives `|S(d²)| ≤ 2√p`), a finite check for `p < 29`, and Hensel for units.
  - Then the classes are translated into the bits of `E1`, `E2`, `(R)` and `twoAdicRows 5`, reusing
    `legBit`, `lam8` and `mu8`, followed by the count bijection `sols ≃ Sel₂(d)`.
- **Checks.**
  - End-to-end: local solubility from sampled `ℚ_p`-points against the system, on 30 values `d ≡ 5`:
    40,512 pairs, 0 mismatches.
  - The 2-adic witness table checked symbolically, and on 250 values of `d`.
  - The `𝔽_p` statement for all `p < 400`.
  - Jacobsthal's identity for all `p < 600`.
- **Mathlib v4.35.0.**
  - Present: Hensel (`hensels_lemma`), `unitCoeff`, `toZMod`/`toZModPow`, Legendre/Jacobi symbols,
    `quadraticChar`, `jacobiSum_nontrivial_inv`, and the Weierstrass group law.
  - Missing: Hilbert symbols, square classes of `ℚ_p`, `Σχ(quadratic)`, any 2-descent or Selmer group
    of a curve, `Fintype E(𝔽_q)` and Hasse. All gaps that Proposition 0 needs are short.
- **Lean probes (compiled, standard axioms only).**
  - `Probe.lean`: both Hensel halves of the square criterion (`u ≡ 1 mod 8` in `ℤ₂`; residue square
    for odd `p`), about 75 lines.
  - `ProbeQ.lean`: Lemma Q, `Σ_ξ χ((ξ−e)(ξ−e′)) = −1`, about 35 lines, compiled on the first attempt.
- **Plan.**
  - Nine files, about 2,500–4,000 lines in total. Slot-k §4.3 estimated "months"; that assumed
    cohomology and local images, which are not needed.
  - First step: `loc_padic_dvd_iff` (Lemma B), with success criterion ≤ 600 lines, no `sorry`,
    standard axioms.

## Ranking

| Rank | Route | Payoff | Main obstacle | First test | Chance |
| --- | --- | --- | --- | --- | --- |
| 1 | R1: full Proposition 0, hypothesis `CR₃^Sel` | explicit system leaves the trust boundary; hypothesis = textbook `Sel₂` + "Selmer rank 3 ⇒ `Ш[2]=0`" | volume: the 2-adic case analysis, Lemma J, bit bookkeeping | `loc_padic_dvd_iff` in ≤ 600 lines | high |
| 2 | R3: hypothesis "`C_d(ℚ)` infinite" (`d` congruent) | deep input exactly in TYZ's form | full 2-descent homomorphism (repo has only the 2-isogeny `kummer`), Mordell–Weil for `C_d/ℚ` | `δ₂` additive on `shortCurve (−d²)`, ≤ 400 lines | medium |
| 3 | R2: bad places only, good primes cited | as R1, plus one STANDARD citation | as R1 minus the good-prime files | as R1 | high, but dominated by R1 |

## Open questions

- Silverman's exact numbering was not rechecked here. That includes X.1.4 (formula for the connecting
  map, as used by rv-slot-k-descent §1.1), X.3 (2-coverings) and the X.4 statement on local images at
  good primes. They are marked UNCHECKED where they are cited by number.
- The match of Kriz Theorem 10.13, and of TYZ 3.5(2) + GZK, with `CR₃^Sel` relies on tyz-5b and
  pc-audit. This task did not recheck them.
- Should Proposition 0 also cover `d ≡ 1, 3, 7 (mod 8)`? It is not needed for the main theorem. It
  would need three more witness tables at 2; the generators are in rv-slot-k-descent §1.4.
- Does the repo's 2-isogeny machinery (`kummer_eq_one_iff`, `rescale_phi_phi`) give `ker δ = 2C_d(ℚ)`
  cheaply? This decides the cost of R3.

## Suggested follow-up tasks

1. **nt-prop0-lean-B**: `Covering.lean` (`Loc`, `Sel2`, `CertifiedRankSel`, and `certifiedRank_of_sel`
   with Proposition 0 as a hypothesis), `PadicSquare.lean` and `BadOdd.lean` up to
   `loc_padic_dvd_iff`. This is the first test of §4.4.
2. **nt-prop0-lean-J** (in parallel, no `p`-adics): Lemma J over `ZMod p`, the count
   `8N ≥ p − 15 − |S|`, and the small-prime Boolean checker.
3. After 1: `Two.lean` (Lemma T), then `Good.lean`, `Bits.lean` and `Prop0.lean`, and a `Main.lean`
   variant with `CertifiedRankSel`.
4. **nt-prop0-r3** (scoping): `δ₂` additivity, `ker δ = 2E` and Mordell–Weil for `C_d/ℚ` via
   `AddCommGroup.fg_of_descent'`, following `mordellWeilE`.
