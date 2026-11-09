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
| §3.3 remark 1 (every small prime divides `v`) | CORRECT; the size `K_A ≈ |A| + 71` is wrong |
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
