# rs-pole: pole completeness (PC) and the restricted converse (RC)

Deliverable: `docs/research/rs-pole.md`. Scripts: `scratch/rs-pole/`.

## Summary

**Uses.** PC is applied in exactly two places, `ZInQ.Mult.slope_complete` and
`ZInQ.Assembly.test_complete`. In both, the input is `B = R₀·s(q)²`:

- `R₀` is fixed by the slope `t`, resp. the integer `n`;
- `s(q)` depends on the free witness `q`, which is chosen by weak approximation.

So the square class of `B` is fixed and only one `q` per instance is needed. (VERIFIED)

**Reformulation.** Write `β = sqf(mB)`, `θ = sqf(m(m − B))` and `g_β(t) = β(βt² − 1)(βt² + 3)`.
Then `Φ(B)` holds if and only if, for some signed divisor `m` of 2730, there are
`t₁, t₂ ∈ ℙ¹(ℚ)` with `θ g_β(t₁) g_β(t₂) ∈ ℚ²`. This is the rational-point problem on a
Kummer-type K3 surface. Witnesses are explicit from `(t₁, t₂)`; this was checked exactly with
`Q_pole = 0` in ℚ.

- Only the abscissa class `β` matters. The manuscript's full Kummer class `(β, 1)` is stronger
  than needed.
- `θ = 1` is trivial via 2-torsion.
- A one-curve sufficient condition: `E_{B(m−B)}` has a point with abscissa in `mBℚ*²`.

**What the descent actually uses.** RC is needed for only two curves per input, `E_n` and
`E_{nθ}`, with `n` free in an infinite family. Even there, positive rank suffices once the
2-Selmer group is minimal. Two smaller inputs can also go:

- Kolyvagin is not needed after RC; Gross–Zagier suffices.
- BCDT can be replaced by modularity of `X₀(24)` plus twisting.

**Explicit points.** No explicit-point route exists. The proof of the obstruction lemma is
`p`-adic, so any algebraic family of witnesses must avoid a `p`-adic neighborhood of `q = ∞` at
every contact prime. Small-height search finds nothing for realistic inputs, because `θ` has
prime factors of about 20 digits.

**Main finding.** Kriz (arXiv:2002.04767v5, Thms 9.23, 10.13, 10.17(2)) proves for every
congruent number curve `y² = x³ − d²x`: `corank Sel_{2^∞} ≤ 1` implies rank = analytic rank
= corank and Ш finite. This is precisely RC for the congruent-number family, for all `d`, with
no congruence condition. Hence Route K:

- Replace `x + 3ℓ` by `x + ℓ` in `Q_pole`.
- Soundness (Lemma 5.1) holds verbatim with the same `S₀`.
- PC follows from an elementary descent plus Poonen–Stoll plus Kriz's theorem.

Route K would make the manuscript's roughly 8,000-line, unrefereed RC proof (Sections 7–9,
Appendices E–G) unnecessary.

**Evidence for the descent in Route K.** An exact complete 2-descent (checked against PARI's
`ellrank` on 38 curves) finds a suitable `(m, n)` for 30 of 30 random admissible inputs:

- 24 inputs need no auxiliary prime, so only one curve needs the converse;
- 6 need one auxiliary prime;
- each search takes at most 2 s.

For two found `n`, PARI's generator has the predicted abscissa class.

**The manuscript's own family.** The same search for `E_ℓ` gives 30 of 30, but only 4 solutions
lie in RC's stated domain `ℓ ≡ 11 (mod 12)`.

## Ranking

1. **Route K** (congruent curves plus Kriz). Chance medium-high. The main risk is the uniform
   combinatorial descent lemma (Monsky-matrix analogue of manuscript lines 1035–1061). The
   second risk is that Kriz's theorem is, as far as checked, a preprint.
2. **Route L.** After K, replace `PoleCompleteness` in Lean by a narrower concrete hypothesis
   ("Selmer-minimal congruent twist has a point with prescribed abscissa class") and prove the
   descent in Lean from Mathlib's Dirichlet theorem and reciprocity.
3. **K with Tian–Yuan–Zhang** (Asian J. Math. 2017, published) in place of Kriz. Its hypotheses
   are unchecked.
4. **A published 2-converse for `E_ℓ`.** None known; low chance.
5. **Nonvanishing instead of a converse.** Low chance.
6. **Explicit points.** Very low chance, because of a structural obstruction.

Recommendation: prove the congruent-curve descent lemma stated in §4.1 of the note, and audit
Kriz's Theorem 10.13 hypotheses.

## Open questions

- The publication status of Kriz arXiv:2002.04767. Are there hidden hypotheses (the small-`f₀`
  cases are handled by LMFDB lookup in the proof)?
- The exact hypotheses of Tian–Yuan–Zhang. Their text could not be retrieved.
- Can the uniform descent lemma for `C_ℓ` be proved as cleanly as the manuscript's matrix
  argument for `E_ℓ`? Does the 2-adic bookkeeping always leave a valid `m`? It did on all 30
  samples.
- Can the freedom in `q` (PC⁻) replace the auxiliary primes entirely? The one-curve condition
  already worked for 24 of 30 inputs.

## Suggested follow-up tasks

1. **cong-descent.** Write and prove the descent lemma for congruent number curves:
   for admissible `(β, θ)`, find `m` and `n = βn′` with `C_n` and `C_{nθ}` Selmer-minimal and
   containing the class `β`. Use `scratch/rs-pole/selmer_descent.py` as an oracle.
2. **kriz-audit.** Source-check Kriz's Theorems 9.23, 10.13 and 10.17 (hypotheses, the LMFDB
   step, publication), in the style of the theorem-application audit.
3. **pole-curve-switch (Lean).** Change `polePoly` and `poleT1`/`poleT2` to `x + ℓ`. Add a
   congruent-curve copy of `poleSystem_no_negative_odd_valuation`, and check that the size
   majorants and the parity lemmas still close. Lean work, one process at a time.
4. **narrow-hypothesis (Lean).** State the concrete arithmetic hypothesis of Route L, and derive
   `PoleCompleteness` (new curve) from it plus the descent lemma, with the descent first left as
   `sorry`.
