# rs-global report: the architecture

Deliverable: `docs/research/rs-global.md`. Scripts: `scratch/rs-global/` (see its README).

The note builds on the per-hypothesis notes rs-height, rs-pole and rs-pattern (on their branches).
It rechecks the facts it uses and adds the comparison across hypotheses and across the three
constructions.

## Findings

1. **Two layers, the same in all three constructions.**
   - Layer A is arithmetic on the labels `[n]P₀`: addition, multiplication, then computably
     enumerable relations.
   - Layer B identifies the rational scalar: support control, a height bound, then approximation
     to a precision computed in Layer A.

   The 10/11 inputs map to 11/5 as follows:
   - rank one becomes G, now a Lean theorem;
   - pole parity splits into Lemma 5.1 (elementary) and PC (narrower than 10/11's "Φ holds on all
     integers");
   - the five-point height becomes the six-contact H;
   - the prime patterns become 22P.

   CAT is new in 11/5 and serves only the size bounds.
2. **Which roles force which inputs** (VERIFIED in Lean and in the manuscript).
   - Soundness uses only H, once per layer.
   - Completeness uses PC in both layers and 22P only in multiplication.
   - Layer B consumes Layer A in both directions: `value_relation_iff_of` takes
     `SpecMultiplicationExact`, and `value.test` makes one `multiply` call, for `κn`. So 22P is a
     hypothesis of the value relation even though no Layer B lemma opens it.
   - The variable shift `κ` keeps prime patterns out of Layer B. The fixed shift `c_*` forces them
     into Layer A. A witness shift there is circular, since controlling it needs label
     multiplication or an order on labels.
3. **Why the inputs are deep: three kinds, each tied to a role.**
   - **K1, points on genus-one twists.** A parity device `y² = x·∏(x − a_i e)` controls every prime
     only if the number of parameter roots is even, so genus `≥ 1`. VERIFIED, elementary, with a
     numerical check. A fixed curve has only finitely many abscissa classes.
   - **K2, a uniform effective height bound.** Full valuation control is equivalent to the
     theorem itself. Cusps break the step from parity to good reduction, and isotrivial families
     lose the height, so the family must live over a compact Shimura curve, and its heights are
     bounded through modularity.
   - **K3, prime patterns.** Multiplication of labels is not algebraic (rigidity; the
     multiplication graph is Zariski dense in `E³`), and the fixed-shift test needs each tested
     prime to be good.

   K1 and K2 are plausibly unavoidable in any parity architecture. K3 is specific to the
   local-test mechanism for multiplication, but no alternative is known.
4. **Quantitative facts** (VERIFIED by computation).
   - 99.95% of the 292,890,231,904 witnesses sit inside the 8,332,156 copies of the
     multiplication template, and 74.7% inside test groups. One more witness in the template costs
     8.3·10⁶ variables, and one more test group per slope costs 3.6·10¹⁰.
   - 42 of the 82 audit records serve only PC and RC; 24 serve only H.
   - Effectivity of H is forced by the size bounds of `FrozenTarget`, not by definability: for the
     bound-free statement an ineffective constant would suffice.
5. **A new contact set.** The Shimura mechanism of H also works with five contacts.
   `J₅(u) = 4(u − 1)²/(u³(2 − u)³)` pulls `ℙ¹_j(4, 6, 2)` back to `ℙ¹_u` with cone points exactly
   at the consecutive integers `−1, 0, 1, 2, 3`, and it is the only degree-6 solution with rational
   cone points (exact computation over the four passports). It matches the count of the preprint's
   five-point height estimate. Transferring the proof of H to it is SPECULATIVE, and the payoff is
   small: a 10-form pattern, and possibly one test group per slope fewer.
6. **Rejected routes, with reasons:**
   - the 3-adic identification of 10/11: it adds Koenigsmann/Hasse–Minkowski, which are not in
     Mathlib, and needs Φ on all integers;
   - quadratic-form architectures: they control only finitely many primes per algebra, and
     weak-approximation varieties satisfy Mazur's conjecture;
   - an ineffective height bound;
   - a witness shift in multiplication;
   - more places or a larger shift: good-prime density in the Chebotarev class rises from 0.856 to
     0.996 as the shift absorbs the primes up to 100, but the bottleneck is that the values must be
     prime;
   - a different label curve;
   - arithmetic on scalars.

## Ranking (order of attack after CAT)

1. **Route K on paper** (congruent number curves with Kriz's 2-converse replacing RC): the uniform
   descent lemma for `C_n`, `C_{nθ}`, and an audit of Kriz's Theorem 10.13. Largest payoff: it
   replaces about 8,000 unrefereed lines and 39 records. Chance medium. **Recommended single next
   step.**
2. **Minimal interface in Lean** (H_min, 22P₂, the gcd relaxation). Chance high, payoff small;
   H_min becomes admissible once effective Dirichlet proves `Hmax_lt_D` and `cstar_lt_D`.
3. **Route L**: the descent in Lean from Mathlib's Dirichlet theorem and reciprocity, with PC
   replaced by a Kriz-form hypothesis. Medium, given 1.
4. **H, CM branch** (rs-height R5.3). Medium; removes 3–4 records.
5. **Five contacts (A3).** Low payoff.
6. **22P below GTZ** (literature). Low.

H and 22P remain hypotheses for the foreseeable future: modularity and Green–Tao–Ziegler are far
beyond Mathlib.

## Open questions

- Does the proof of Theorem 4.1 go through verbatim with `J₅`? What are the constants, and is the
  exponent below 25?
- Can an odd number of finite contacts be accommodated in the slope normalization
  `R₀ = ηF(t)/(t − 1)⁸` without making the denominator a sixth tested form?
- Is there any multiplication certificate whose witnesses exist by a theorem weaker than a linear
  prime pattern, for example Dirichlet or Chebotarev alone? Rigidity (C5) only says that some
  arithmetic witness is needed.
- Kriz's theorem: publication status, and hidden hypotheses (rs-pole's open question, which ranks
  1 and 3 depend on).

## Suggested follow-up tasks

- **cong-descent** (paper): the uniform descent lemma for congruent number curves, as in §5.4 of
  the note, with `scratch/rs-pole/selmer_descent.py` as oracle.
- **kriz-audit** (paper): a source check of Kriz's Theorems 9.23, 10.13 and 10.17 in the style of
  the theorem-application audit.
- **interface-refactor** (Lean): `SixContactMin` and `TwoSlopePattern` in the main theorem, one
  Lean process at a time.
- **height-J5** (paper): redo the proof of Theorem 4.1 with `J₅` and contacts `{−1, 0, 1, 2, 3}`,
  and record the constants. Do this only if a construction redesign is planned.
