# Referee report on `nt-22p.md`: Proposition AP, Proposition D and the Green–Tao step

Scope: §2 (Proposition D and the CM description of the good slope primes), §3.3 (the
hypothesis 22P_AP and Proposition AP), §3.4 (Green–Tao 2008 and the trust-base table) of
`docs/research/nt-22p.md`, compared with `ZInQKernel/Hypotheses/PrimePattern.lean`,
`ZInQKernel/Multiplication/Completeness/{PatternSlopes,TwoSlope,SlopeCompleteness,PoleValuations,Core}.lean`,
`ZInQKernel/Hypotheses/Pole.lean` and the TeX source of Green–Tao, arXiv math/0404188v6.
Lemma P and the modified slope-completeness argument of §3.2 are outside this report. I checked
Lemma P(1), which Proposition AP feeds directly, and I take the rest of §3.2 as given.

Notation is that of the note: `𝒞 = {0, −15, −20, −24, −30, −60}`, `T = 𝒞 ∪ {1}`, `A′ = A + 10`,
`S_A⁺ = T ∪ (A′ − T)`, `M = max S_A⁺`, `K_A = M − min S_A⁺`, `G` the good slope primes
(`ZInQ.GoodSlopePrime`), `G′ = {p ∈ G : p > max S_b}`, `B_ℓ = 4` on `S_ht` and `1` on the
catalogue.

## Verdict

**Proposition AP is proved as written**, given the modified slope completeness of §3.2 (field 2′
in place of field 2), which this report does not referee. Every step of §3.3 is correct. The one
numerical slip (the size of `K_A`) does not affect the argument.

**Proposition D is correct** as a proof sketch. Its two analytic inputs (Hecke's prime ideal
theorem for `ℚ(i)`, or only the prime number theorem in progressions, and a two-dimensional upper
bound sieve uniform in `ℓ`) are standard, and the sieve is the manuscript's own (lines 1600–1642),
transposed from prime values of a form to primes up to `N`. It still has to be written out.

**The Green–Tao step is correct.** Theorem 1.2 of Green–Tao 2008 is quoted correctly: it
concerns positive *relative upper* density among the primes, and its progressions are genuine,
non-constant progressions of primes. After reversal they give `x ≥ 1`, `v ≥ 1`, and `x > N` for
any prescribed `N` once the theorem is applied to `G ∩ (N, ∞)`.

**The trust-base claim is right in substance, with qualifications.** The deep input of the
hypothesis drops from the Green–Tao–Ziegler machinery to Green–Tao 2008. But (i) the Lean main
theorem rests on 22P_AP only after the Lean work of Route 1 (field 2′, the Lemma P branch, the
residue-class weak approximation). Until then, the kernel-checked derivation of the slope
representation from 22P₂ is traded for unformalized elementary steps. (ii) Proposition D is still
a sketch. (iii) Green–Tao 2008 prove Theorem 1.2 only in outline (their §10 leaves the details to
the reader), and the exposition the note proposes to follow proves only Theorem 1.1.

No finding is critical or major. Section 2 lists the findings; Section 7 lists the repairs.

## 1. Summary of the steps examined

| Step | Verdict |
| --- | --- |
| §2.1 CM description of `G` for `p > 324` | CORRECT (by hand, and by computation for all `325 ≤ p ≤ 2·10⁵`) |
| §2.2 Euler product and natural density | CORRECT (sketch; computation to `3·10⁷`) |
| §2.2 sieve for `ℓ > L` | CORRECT (it is the manuscript's sieve, transposed) |
| §2.2 positivity without Hecke | CORRECT |
| density of `G′` is relative to the primes | CORRECT |
| §3.3 the set `S_A⁺`, indexing in a progression of length `K_A + 1` | CORRECT |
| §3.3 lowest terms | CORRECT |
| §3.3 field 1 | CORRECT |
| §3.3 signs `F(t₁) > 0`, `F(t₂) > 0` for every integer `A` | CORRECT (including `A′ = −59, −60`) |
| §3.3 field 2′ | CORRECT (case split checked; Lemma P(1) checked) |
| §3.3 fields 3 and 4 | CORRECT (same argument as `goodSlope_of_primeValues`) |
| §3.3 the constant slope `−10` | CORRECT (kernel-checked `goodSlope_neg_ten`) |
| §3.3 remark 1 (every small prime divides `v`) | CORRECT; the stated size of `K_A` is wrong (F1) |
| §3.3 remark 3 (Lemma P needed only on `S₀`) | CORRECT |
| §3.4 statement of Green–Tao 2008, Theorem 1.2 | CORRECT (checked against the TeX source) |
| §3.4 22P_AP from Theorem 1.2 and Proposition D | CORRECT |
| §3.4 trust-base table | CORRECT in substance; incomplete (findings F3–F5) |
| §3.2 Lemma P(2), P(3) and the modified slope completeness | UNCHECKED here (outside this report) |

## 2. Findings

**F1 (minor, cosmetic).** §3.3, remark 1, says `K_A ≈ |A| + 71`. In fact
`max S_A⁺ = max(1, A′ + 60)` and `min S_A⁺ = min(−60, A′ − 1)`, so

- `K_A = A′ + 120 = A + 130` for `A′ ≥ −59`,
- `K_A = 2 − A′ = −A − 8` for `A′ ≤ −60`,

with minimum `61` at `A′ = −59`. Only the qualitative statement (`K_A → ∞`) is used, so nothing
breaks. A useful consequence the note does not state: every progression used has at least 62
terms, so `v` is divisible by every prime `≤ 61`. In particular `8 | v`, since all terms are
`≡ 1 (mod 8)`. So the delicate case `ℓ = 2`, `v₂(v) ≤ 2` of Lemma P never occurs in
Proposition AP.

**F2 (minor, wording).** "All fourteen numbers `u − c′v` are primes of `G′`": `S_A⁺` has fewer
than fourteen elements when `T` and `A′ − T` meet (for instance `A′ = 0`). Then the two variable
slopes share a contact prime. This is harmless: `GoodSlope` is a condition on each slope
separately, and the consumer (`slope_complete`, `Core.lean:17`) treats the three slopes
independently, with private groups. The Lean proof from 22P₂ already allows such coincidences.

**F3 (minor, trust base: the reference for Theorem 1.2).** In the TeX source, Theorem 1.2
(`sz-primes`) is stated in §1, but §10 says only that "our method also extends to prove
Theorem 1.2"; the one change is a pigeonholed residue class `b mod W`, and "we leave the details to
the reader". The Conlon–Fox–Zhao exposition (arXiv:1403.2957), which the note names as the route a
formalization would follow, gives a complete proof of Theorem 1.1 only. It lists Theorem 1.2 among
the "extensions". The modification is routine and Theorem 1.2 is universally accepted. Still,
the trust-base table should cite it as "Green–Tao 2008, Theorem 1.2 (proof outlined in §10)" and
add a source with a complete proof of the dense-subset form, or note that the relative Szemerédi
theorem of Conlon–Fox–Zhao (arXiv:1305.5440, Theorem 1.1 there) plus the `W`-trick with a
pigeonholed class gives it. The note's §3.1 still calls the theorem number UNCHECKED while §3.4
says VERIFIED. The number is 1.2: the theorem counter is tied to subsections, and none precedes it
in §1.

**F4 (moderate, trust base: formalization status).** The table at the end of §3.4 lists
"Lemma P and the modified choice of `q`" and "Proposition AP" as "elementary, VERIFIED by hand".
For the Lean main theorem the comparison should be stated as follows.

- Today `Main.lean` derives `SlopeRepresentation` from 22P₂ in the kernel
  (`slopeRepresentation_of_twoSlopePattern`) and from 22P (`slopeRepresentation_of_fixedPrimePattern`).
- From 22P_AP, `SlopeRepresentation` (with field 2′) needs three new Lean pieces. First, field 2′
  in `GoodSlope`. Second, a new `part1` in `pole_input_valuations`: field `old` is used only there,
  at `PoleValuations.lean:126`, and `GoodSlope.old_le_Cp` has no consumer. Third, a weak
  approximation that hits a residue class at the primes of `S_pole`.

So the hypothesis becomes cheaper only once these pieces are kernel-checked. Before that, the
step from the hypothesis to the slope representation is paper mathematics. The note's Route 1
plans exactly this work; the table should say that its rows for Lemma P and Proposition AP are
"to be formalized", not part of the trust base.

**F5 (minor, Proposition D is a sketch).** The note marks Proposition D as a transposition of
the manuscript's argument, not written out, and that is accurate. Two points must be explicit in
the write-up.

- *The sieve range `L < ℓ ≤ N^{1/8}`.* It needs an upper bound `≪ N/(ℓ² log N)`, uniform in `ℓ`,
  for the primes `p = a² + b² ≤ N` with `a ≡ 0`, `b ≡ b₀ (mod ℓ)`. The manuscript obtains it from
  its two-dimensional Selberg sieve, (`eq:prime-selberg`) and
  (`eq:prime-truncated-denominator`). Brun–Titchmarsh for primes of `ℤ[i]` in a residue class
  modulo `ℓ` gives it as well. Trivial counting does not suffice: without the factor `1/log N`
  the sum over `ℓ > L` is `N/L`, which is not small against `π(N)`.
- *The tail `ℓ > N^{1/8}`.* The lattice count gives `≪ N^{7/8} + √N log N` (as in the manuscript).
  The note's display omits the second term, which is dominated anyway.

The "Hecke avoided" variant is sound: the congruences `p ≢ −1 (mod ℓ)` for odd `ℓ ≤ L` leave
relative density `≫ 1/log L` by Mertens' theorem, and the tail is `O(1/L)`. It still uses the
same uniform sieve for `ℓ > L`. So "only the rational prime number theorem in progressions and the
elementary sieve" is accurate, provided "elementary sieve" means the two-dimensional Selberg sieve
of the manuscript.

**F6 (minor, wording).** §3.4 says Green–Tao 2008 uses Szemerédi's theorem "in its quantitative
finite form". The source says the opposite about quantities: the proof needs the finitary
weighted form (a positive proportion `c(k, δ)` of progressions, their Proposition 2.3) but "we will
not need any quantitative estimates on `N₀(δ, k)`". Say "finitary (Varnavides) form, with no
bounds".

## 3. Proposition AP, step by step

Fix `A`, and let `x, x + v, …, x + K_A v` be a progression in `G′` with `x ≥ 1`, `v ≥ 1`. Put
`u = x + Mv`, `t₁ = u/v`, `t₂ = A′ − u/v`, `t₃ = −10`.

**The set and the indexing.** For `c′ ∈ S_A⁺`, `u − c′v = x + (M − c′)v` with
`0 ≤ M − c′ ≤ K_A`, a term of the progression. CORRECT. The twelve contact numerators are
`u − cv` (for `t₁`) and `u₂ − cv = −(u − (A′ − c)v)` with `u₂ = A′v − u` (for `t₂`); the two
numerators of `t − 1` are `u − v` and `−(u − (A′ − 1)v)`. All fourteen indices lie in `S_A⁺`.
CORRECT. Also `t₁ + t₂ + t₃ = A′ − 10 = A`.

**Lowest terms.** A prime dividing `u` and `v` divides `x` and hence every term. The terms are at
least 62 distinct primes, so no prime divides two of them. CORRECT. (Lowest terms is used only to
state Lemma P; the Lean proof of fields 1, 3, 4 does not need it.)

**Field 1.** `t₁ − c` and `t₁ − 1` have nonzero numerators (primes); likewise `t₂`. CORRECT.

**Signs.** `t₁ = M + x/v > M ≥ 1`, so all six factors of `F(t₁)` are positive. For `t₂`,
`t₂ = (A′ − M) − x/v`. If `A′ ≥ −59` then `M = A′ + 60` and `A′ − M = −60`. If `A′ ≤ −60` then
`M = 1` and `A′ − M = A′ − 1 ≤ −61`. At the switch `A′ = −59` both formulas give `M = 1`. In all
cases `t₂ < −60`, so all six factors `t₂ − c` (`c ≥ −60`) are negative and `F(t₂) > 0`. CORRECT,
for every integer `A`, with no condition on the progression. Then `slope_complete` chooses
`η = 1` for both slopes (it takes `η` with `R₀ > 0`, `SlopeCompleteness.lean`), as Lemma P
requires. The constant slope has `F(−10) = −7·10⁶ < 0`, so `η = −1` there, but it does not use
Lemma P.

**Field 2′.** Let `ℓ ∈ S_b` and `e = v_ℓ(v)`. The fourteen terms exceed `max S_b`, so they are
`ℓ`-units. Hence `v_ℓ(t − 1) = −e` and
`v_ℓ(F(t)/(t − 1)⁸) = v_ℓ(v²F(u, v)/(u − v)⁸) = 2e`, for both variable slopes. Field 2 asks
`e ≤ B_ℓ` and `2e ≤ 8B_ℓ`, so it holds iff `e ≤ B_ℓ`. Otherwise `e ≥ B_ℓ + 1 ≥ 2`, and `e ≥ 5`
at `ℓ = 2` (where `B₂ = 4`). The hypotheses of Lemma P then hold: the seven numerators are units,
`F(t) > 0`, and `e ≥ 3` at `ℓ = 2`. CORRECT.

I also checked Lemma P(1), the only part of Lemma P that Proposition AP feeds. Write `w` for the
numerator (`u` or `u₂`). Then
`R₀ℓ^{−2e} = (vℓ^{−e})² w⁶ (w − v)^{−8} ∏_c(1 − cv/w)`. The first three factors are squares of
`ℓ`-units, and each `1 − cv/w ≡ 1 (mod ℓ^e)`. So `R₀` is a square in `ℚ_ℓ` for odd `ℓ`, and
for `ℓ = 2` once `e ≥ 3`. CORRECT; also confirmed numerically (Section 8).

**Fields 3 and 4.** In `TwoSlope.lean`, `goodSlope_of_primeValues` proves fields 1, 3 and 4 from
two facts only: the six contact numerators are, up to sign, primes of `G` outside `S_b`, and
`u − v ≠ 0`. The hypothesis `hold` (the valuation bounds at `S_b`) enters only the proof of
field 2. A prime `p ∉ S_b` dividing `v` gives `v_p(t − c) = −v_p(v) < 0` for every `c`: it cannot
divide a numerator, since `u` and `v` are coprime. A prime `p ∉ S_b` dividing a numerator is that
numerator's prime and divides no other numerator, since the terms are distinct primes. So the
odd contact primes of `t_j` outside `S_b` are exactly its six numerator primes, each with contact
valuation 1, and they are good. CORRECT: the Lean argument carries over verbatim, with the
hypothesis `hold` dropped.

**The constant slope.** `goodSlope_neg_ten` is kernel-checked with the original field 2, which
implies 2′. CORRECT.

**Remark 3 of §3.3.** `ZInQ.PoleCompleteness` (`Hypotheses/Pole.lean:62`) asks for a square
reduced denominator, `0 < B < 1/2` and `v_p(B) ≥ 4` only for `p ∈ S₀`. At `ℓ ∈ S_b ∖ S₀` with a
pole, `v_ℓ(B) = 2v_ℓ(ℓ₀) + 2v_ℓ(a) + 2e − 2v_ℓ(Θ)` is even for every `q`, since `Θ ∈ ℚ`. CORRECT.

**Interface.** `SlopeRepresentation` is consumed only through `slope_complete`, one slope at a
time (`Core.lean:17`). In `slope_complete` the field `old` reaches only `pole_input_valuations`,
whose `part1` turns it into `v_p(B) ≥ 103C_p + 8` on `S_b`. That bound is used only for
`v_p(B) ≥ 4` on `S₀` and for the square denominator. So the replacement of field 2 by 2′ is local,
as the note says. Whether the new `part1` holds is the content of §3.2 (outside this report).

## 4. Proposition D

**The description of `G` (§2.1).** For `p > 324`, `GoodSlopePrime p` holds iff `p ≡ 1 (mod 8)`,
`(7/p) = −1`, and no odd prime `ℓ` divides both `a` and `p + 1`, where `p = a² + b²` with `a` odd.
I checked each step by hand:

- *Splitting.* `r² = 2` is solvable iff `p ≡ ±1 (mod 8)`. For `p ≡ 3 (mod 4)`, `y² = x³ + αx` is
  supersingular, both orders are `p + 1`, and the gcd is `p + 1 > 4`.
- *Twists.* `d₁d₂ = 75² − 2·53² = 7`, so `a₁/a₂ = d₁²/d₂² = d₁⁴/49`. For `p ≡ 1 (mod 4)` this is
  a fourth power iff `7` is a square mod `p`. If it is, the two curves are isomorphic and the gcd
  is `d₁ ≥ p + 1 − 2√p > 4`. If not, the curves are quadratic twists of each other, with traces
  `±τ`.
- *The trace.* `x³ − d²x` splits over `𝔽_p`, so `4 | #E`. Since `p + 1 ≡ 2 (mod 8)`, this forces
  `τ ≡ 2 (mod 4)`, hence `τ = ±2a` with `a` odd (the alternative `±2b` has `b` even). So the orders
  are `p + 1 ∓ 2a`.
- *The gcd.* The orders differ by `4a`, which has 2-adic valuation exactly 2, so the 2-part of the
  gcd is exactly `4`. An odd `ℓ` divides both orders iff `ℓ | a` and `ℓ | p + 1`. Then
  `b² ≡ −1 (mod ℓ)`, so `ℓ ≡ 1 (mod 4)`.

Computation (Section 8): the literal Lean definition (both roots `r`, point counts by brute force
or by PARI) agrees with this description at every prime `325 ≤ p ≤ 2·10⁵`. CORRECT.

**The density.** In `ℤ[i]/ℓ ≅ 𝔽_ℓ × 𝔽_ℓ`, the bad event at `ℓ ≡ 1 (mod 4)` is that the generator
with odd real part lies in `±(1, −1)`: two classes out of `(ℓ − 1)²`, independent of the
conditions modulo 8 and 7 on the norm. Hecke's theorem for the ray class groups of `ℚ(i)` gives
the density `(1/8)∏_{ℓ ≤ L}(1 − 2/(ℓ − 1)²)` for the primes with no bad `ℓ ≤ L`. Together with
the uniform tail bound `O(1/L)` (F5), this gives the natural density
`(1/8)∏_{ℓ≡1 (4)}(1 − 2/(ℓ − 1)²) ≈ 0.1060`. Numerically, the share of good primes among the primes
up to `3·10⁷` is `0.10610`. CORRECT.

**Relative density.** Proposition D is a statement about `|G ∩ [1, N]|/π(N)`, which is exactly the
relative density in Green–Tao's Theorem 1.2. Removing the finitely many primes `≤ max S_b`, or
`≤ N` for any fixed `N`, does not change it. So `G′` and `G ∩ (N, ∞)` have positive relative upper
(indeed natural) density. CORRECT.

## 5. Green–Tao 2008

The TeX source of arXiv math/0404188v6 (the version published in Ann. of Math. 167 (2008)) states
in §1:

> **Theorem 1.2** (Szemerédi's theorem in the primes). Let `A` be any subset of the prime numbers
> of positive relative upper density, thus `limsup_{N→∞} π(N)^{−1}|A ∩ [1, N]| > 0`, where `π(N)`
> denotes the number of primes less than or equal to `N`. Then `A` contains infinitely many
> arithmetic progressions of length `k` for all `k`.

- *Upper or lower density.* Upper density suffices. Proposition D gives more, a natural density.
- *Non-degenerate progressions.* In the proof (of Theorem 1.1, and in §10 for Theorem 1.2) the
  degenerate progressions `r = 0` contribute `O(N^{−1} log^k N) = o(1)` and are discarded. The
  progressions counted are genuine progressions of integers, because their terms lie in
  `[ε_kN, 2ε_kN]` with `ε_k < 1/k`. So the progressions are non-constant and consist of primes in
  `A`. Reversing the order if needed gives `v ≥ 1`, and `x ≥ 1` because the terms are primes.
- *Large first term.* "Infinitely many progressions" alone does not bound the first term from
  below (the difference could grow instead). Applying the theorem to `G ∩ (N, ∞)` gives `x > N`
  directly. This is the form needed for the Lean statement
  `GoodPrimeAP : ∀ K N, ∃ x v, N < x ∧ 0 < v ∧ ∀ j ≤ K, GoodSlopePrime (x + j v)`. The note says
  this ("removing finitely many primes changes nothing").

So 22P_AP follows from Theorem 1.2 and Proposition D. CORRECT. The caveat on the completeness of
the published proof of Theorem 1.2 is F3.

## 6. The trust base

The table at the end of §3.4 compares the AP route with the manuscript's proof of
Proposition 6.2. Here is my assessment.

- *Deep inputs.* The manuscript's proof uses three deep theorems: Green–Tao 2010 (linear
  equations in primes), Green–Tao 2012 (Möbius and nilsequences) and Green–Tao–Ziegler 2012 (the
  inverse theorem for all Gowers norms). On top of these it uses about four hundred lines of its
  own estimates: singular series, a two-variable Selberg sieve, the fibre count, and the unit
  classes of the catalogue. The AP route uses Green–Tao 2008, whose ingredients are Szemerédi's
  theorem in finitary form, the transference principle and the Goldston–Yıldırım correlation
  estimates. Strictly speaking, the AP route's inputs are not a subset of the manuscript's, because
  the 2010 paper does not use Szemerédi's theorem. But Szemerédi's theorem is much older and has
  several independent complete proofs (combinatorial, ergodic, Fourier-analytic and
  hypergraph-theoretic), and it can also be derived from the inverse theorem by the arithmetic
  regularity method. In depth and in auditability the reduction is real. **The claim that the trust base shrinks is correct in substance.**
- *Shape of the hypothesis.* 22P_AP does not mention `A`, the catalogue multipliers or valuations
  at the old primes, only the lower bound on the primes. It is literally a special case of a
  published theorem, applied to a set whose relative density is computed in Proposition D. That
  is a real gain over 22P (multipliers, signs, 22 forms in three variables) and over 22P₂
  (valuation side conditions), for which no published theorem applies directly.
- *What the table omits.*
  - (i) The steps from 22P_AP to the slope representation are paper mathematics until Route 1 is
    formalized (F4). Today the Lean derivation from 22P₂ is kernel-checked, so for the Lean main
    theorem the trust base shrinks only after that work.
  - (ii) Proposition D is a sketch (F5). It belongs to the paper justification of the hypothesis,
    as the manuscript's 400 lines do for 22P, and it has to be written out. It reuses the
    manuscript's sieve, so it adds no new kind of input.
  - (iii) Theorem 1.2 is proved in Green–Tao 2008 only in outline (F3).
  - (iv) The CM facts of record A072 enter only to identify `G` and compute its density.

## 7. Repairs

1. (F1) In §3.3, remark 1, replace "`K_A ≈ |A| + 71`" by
   "`K_A = A + 130` for `A ≥ −69` and `K_A = −A − 8` for `A ≤ −70`, so `K_A ≥ 61`". Add: "every
   progression of `K_A + 1 ≥ 62` primes above `62` has `v` divisible by every prime `≤ 61`; in
   particular `8 | v` (all terms are `≡ 1 mod 8`), so the case `ℓ = 2`, `v₂(v) ≤ 2` of Lemma P does
   not occur."
2. (F2) In the proof of Proposition AP, say "the at most fourteen numbers", and note that a prime
   shared by `t₁` and `t₂` is harmless, because `GoodSlope` and `slope_complete` treat the slopes
   separately.
3. (F3) In §3.1 and §3.4, cite "Green–Tao 2008, Theorem 1.2 (stated in §1; proof outlined in
   §10)", give a reference with a complete proof of the dense-subset form, and make the
   UNCHECKED/VERIFIED labels consistent. The number 1.2 is right.
4. (F4) In the trust-base table, mark the rows for Lemma P, the modified choice of `q` and
   Proposition AP as "to be formalized (Route 1)", and say that until then the derivation of the
   slope representation from the hypothesis is not kernel-checked.
5. (F5) In the write-up of Proposition D, cite the uniform two-dimensional sieve for
   `L < ℓ ≤ N^{1/8}` explicitly (the manuscript's (`eq:prime-selberg`) and
   (`eq:prime-truncated-denominator`), or Brun–Titchmarsh for `ℤ[i]`), and keep the term
   `√N log N` in the tail.
6. (F6) In §3.4, replace "quantitative finite form" by "finitary (Varnavides) form, with no
   bounds needed".

None of these repairs changes a statement or a proof step of Propositions AP or D.

## 8. Computations

All scripts were written for this report: `scratch/rv-nt22p-ap/density.py` and
`scratch/rv-nt22p-ap/apcheck.py`, using Python with exact rationals and PARI/GP 2.17.

| Check | Result |
| --- | --- |
| literal `GoodSlopePrime` (both roots `r`, brute-force point counts) vs CM description, all primes `325 ≤ p ≤ 40000` | 0 mismatches; 450 good primes below `40000` |
| same with PARI `ellcard`, all primes `325 ≤ p ≤ 2·10⁵` | 0 mismatches; 1,925 good primes below `2·10⁵`; good `p ≤ 324`: 17, 41, 73, 97, 241, 257, 313 |
| primes `11 ≤ p ≤ 3·10⁷` (1,857,855 primes) | class share `0.12503`, good share `0.10610`, good/class `0.84860` |
| `∏_{ℓ≡1 (4), ℓ<10⁷}(1 − 2/(ℓ − 1)²)` | `0.84820` (times `1/8`: `0.10602`) |
| Proposition AP: 149 values of `A` (all of `[−80, 60]`, `±10⁶`, `±1000`, `−71…−68`), 3 random progressions each, two seeds, with `v_ℓ(v)` up to 30 at each `ℓ ∈ S₀` | indexing, `t₁ + t₂ + t₃ = A`, field 1, `F(t₁) > 0`, `F(t₂) > 0`, `t₂ < −60`, `v_ℓ(t − 1) = −e`, `v_ℓ(R₀) = 2e`: all hold |
| Lemma P(1) on these slopes, whenever `e > B_ℓ` (7,778 cases) | `R₀` a square in `ℚ_ℓ` in every case |
| control: `ℓ = 2`, `v₂(v) ≤ 2`, `F(t) > 0` | `R₀` a non-square in `ℚ₂` in 200 of 200 samples |

The synthetic progressions in the Proposition AP test are not progressions of primes (a
progression of at least 62 primes above `max S_b` is far beyond computation). They test the
algebra: they are chosen so that every term is a unit at each prime of `S₀`, which is all the
argument uses at the old primes.
