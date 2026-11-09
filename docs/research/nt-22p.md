# The prime-pattern hypothesis 22P: density of good primes, Green–Tao 2008, and the shape of the pattern

Status: research note, 2026-11-09. Each claim carries a mark:
**VERIFIED** (checked against the manuscript, the Lean source or a computation, which is cited),
**STANDARD** (a published theorem whose statement was checked to apply; reference given),
**SPECULATIVE** (an idea, unproved) or **UNCHECKED** (a source that could not be read; the statement
is quoted from memory or from an abstract and must be checked before use).
Manuscript line numbers refer to `diophantine_zq.tex` (11/5 version); audit records are those of
`docs/theorem-application-audit/applications.json`. This note continues `rs-pattern.md` (cited as
[RP §n]) and `rs-global.md` ([RG]); their notation is used throughout.

Notation. `𝒞 = {0, −15, −20, −24, −30, −60}`, `F(t) = ∏_{c∈𝒞}(t − c)`, `F(u, v) = v⁶F(u/v)`,
`K₀ = ℚ(√2)`, `E : y² = x³ − d²x` with `d = 75 − 53√2`, `S_ht = {q ≤ 324}`, `S_b = S_ht ∪ 𝓗`,
`S₀ = {2, 3, 5, 7, 13}` (`ZInQ.poleS0`), `B_q = 4` on `S_ht` and `1` on `𝓗`, `c_* = 4M₀`.
`G` denotes the set of good slope primes (`ZInQ.GoodSlopePrime`): `p` splits in `K₀`, both
reductions of `E` above `p` are good, and their orders `d₁, d₂` satisfy `gcd(d₁, d₂) = 4`.
For a slope `t = u/v` (lowest terms) the slope predicate (lines 1177–1235) uses
`R₀ = ηF(t)/(t − 1)⁸`, `η = ±1`, `a = 1 − R₀q²` with a free rational witness `q`,
`R = ℓ₀²a²R₀`, the normalized tests `C_{gj} = D_{gj}/(R₀^{k_j}(t − 1)^{k_j+1})`,
`W_g = ∏_j(1 + RC_{gj}²)`, `Θ = Tr Σ_g W_g^{−1}` and the pole input `B = R/Θ²`.

## Summary

1. **Density (question 1).** The good primes have a positive natural density, unconditionally:
   about `0.1064` of all primes, `0.850` of the Chebotarev class `p ≡ 1 (mod 8)`, `(7/p) = −1`,
   in agreement with the Euler product `(1/8)∏_{ℓ≡1 (4)}(1 − 2/(ℓ − 1)²) = 0.1060`. The infinite
   family of conditions behind `gcd(d₁, d₂) = 4` costs nothing deep, because `E` has CM by `ℤ[i]`:
   an odd `ℓ` divides both orders iff `ℓ | a` and `ℓ | p + 1` for `p = a² + b²`, and these
   conditions have density `≍ 1/ℓ²`, so small `ℓ` are removed by congruences and large `ℓ` by an
   elementary lattice sieve. This is how the manuscript argues (lines 1554–1642, record A072 for
   the CM identities); it needs no GRH, and I found no gap in it. The full gcd condition is used
   at one place only (`ZInQ.Mult.shift_choice`, through `exists_shift`), and there it is necessary
   for the honest witnesses to exist, so no version with finitely many Chebotarev conditions serves
   the present test. Under the route of item 2 this does not matter: only positive density is needed.
2. **Green–Tao 2008 suffices (question 2).** The obstacle of [RP R4], bounded valuations of the
   common difference `v` at the old primes, disappears once the witness `q` of the slope predicate
   is used: when `t` has a pole of order `e` at an old prime `ℓ` (that is, `ℓ^e ∥ v`) and `η = 1`,
   `R₀` is a square in `ℚ_ℓ` (for `ℓ = 2` once `e ≥ 3`), so `q` can be chosen with `v_ℓ(a)` as
   large as needed, which makes `v_ℓ(B) ≥ 4`. With this change of the completeness proof (the
   polynomial is unchanged), the slope representation follows from a homothetic copy of a 14-point
   set inside `G`, and that follows from Green–Tao 2008 (Szemerédi's theorem in the primes) applied
   to `G`. The Green–Tao–Ziegler inverse theorem, the Möbius–nilsequence theorem and the
   linear-equations asymptotic all leave the proof. The local lemma is proved below (§3.2) and
   tested on 30 samples; the whole chain is SPECULATIVE until written out in full, but every step
   is elementary except Green–Tao 2008 itself.
3. **Fewer forms (question 3).** No: in any construction where a slope is a Möbius function of a
   rational parameter, its six contact values are six pairwise independent linear forms in two
   variables, a system of true complexity 4, out of reach of the circle method. Two non-constant
   slopes are forced (one variable slope plus constants fails for infinitely many `A`), and a
   three-slope identity collapses to the two-slope one. The twelve forms of 22P₂ can, however, be
   placed in a single arithmetic progression, which is exactly what Green–Tao 2008 needs. The
   contact set has a Möbius symmetry group of order 12 (VERIFIED), so the orbit of a good slope
   consists of good slopes with the same primes; this does not reduce the pattern.

Recommendation: state the hypothesis as the progression form **22P_AP** (§3.3), prove the slope
representation from it in Lean with the modified choice of `q`, and record Green–Tao 2008 as its
only deep input (§5, rank 1).

---

## 1. The interface

The completeness proof consumes 22P only through `ZInQ.Mult.SlopeRepresentation`: every integer
`A` is `t₁ + t₂ + t₃` with `GoodSlope 0 tⱼ` (VERIFIED, [RP §1.2, §2.1], `PatternSlopes.lean`).
`GoodSlope B₀ t` has four fields (`PatternSlopes.lean:27`):

1. `t ∉ 𝒞`, `t ≠ 1`;
2. `old`: for `q ∈ S_b`, `|v_q(t − 1)| ≤ B_q` and `|v_q(F(t)/(t − 1)⁸)| ≤ 8B_q`;
3. `contact`: every odd contact prime `p ∉ S_b` is a good slope prime with all positive contact
   valuations equal to 1;
4. `few`: at most six such primes.

The two-slope form `ZInQ.TwoSlopePattern` (22P₂) gives the representation through
`t = (u/v, A + 10 − u/v, −10)` (`Mult.slopeRepresentation_of_twoSlopePattern`, `TwoSlope.lean`).
It asks that the twelve numbers `u − c′v`, `c′ ∈ 𝒞 ∪ (A + 10 − 𝒞)`, be good slope primes above 324
outside the catalogue, and that `v`, `u − v`, `u − (A + 9)v` have valuation at most 4 at `q ≤ 324`
and at most 1 at the catalogue primes (VERIFIED, `PrimePattern.lean`). The last clause serves
field 2 only.

Pole completeness, which the slope predicate feeds, asks of `B`: square reduced denominator,
`0 < B < 1/2`, and `v_p(B) ≥ 4` for `p ∈ S₀ = {2, 3, 5, 7, 13}` (`ZInQ.PoleCompleteness`,
`Hypotheses/Pole.lean:62`; manuscript Theorem 5.2). VERIFIED. At old primes outside `S₀` it asks
only that a negative valuation be even.

---

## 2. The density of good slope primes (question 1)

### 2.1 The CM description

For `p > 324` (VERIFIED, manuscript lines 1554–1598, record A072, and `scratch/nt-22p/density.py`):

- `p ∈ G` forces `p ≡ 1 (mod 8)`: splitting in `K₀` gives `p ≡ ±1 (mod 8)`, and for `p ≡ 3 (mod 4)`
  both reductions are supersingular with `d₁ = d₂ = p + 1`, so `gcd(d₁, d₂) = p + 1 > 4`.
- `p ∈ G` forces `(7/p) = −1`: the two reductions of `d` have product `N(d) = 7`; if `7` is a
  square mod `p` the two reduced curves are isomorphic and `gcd = d₁ > 4` by Hasse.
- For `p ≡ 1 (mod 8)` with `(7/p) = −1`, write `p = a² + b²` with `a` odd. Then
  `{d₁, d₂} = {p + 1 − 2a, p + 1 + 2a}`, the 2-part of `gcd(d₁, d₂)` is exactly 4, and an odd prime
  `ℓ` divides both orders iff `ℓ | a` and `ℓ | p + 1`, i.e. iff `ℓ | a` and `b² ≡ −1 (mod ℓ)`
  (which forces `ℓ ≡ 1 mod 4`).

So `G` is the set of primes `p ≡ 1 (mod 8)`, `(7/p) = −1`, with no odd `ℓ | gcd(a, p + 1)`. In
terms of a Gaussian prime `π = a + bi` above `p`, and `ℓ = λλ̄` split in `ℤ[i]`, the bad event at
`ℓ` is `π ≡ ±(1, −1)` in `(ℤ[i]/ℓ)^× ≅ 𝔽_ℓ^× × 𝔽_ℓ^×`: two classes out of `(ℓ − 1)²`.

The computation `scratch/nt-22p/density.py` (PARI/GP, all primes `11 ≤ p ≤ 3·10⁶`) finds:

| Quantity | Value |
| --- | --- |
| point-count definition vs CM description, all primes `< 2·10⁵` | no mismatch (1,925 good primes, as in [RP §2.2]) |
| share of the class `p ≡ 1 (8)`, `(7/p) = −1` among primes | 0.1251 (expected `1/8`) |
| share of good primes among primes | 0.1064 |
| share of good primes in the class | 0.8504 |
| Euler product `∏_{ℓ≡1 (4)}(1 − 2/(ℓ − 1)²)` | 0.8482 |

VERIFIED (computation).

### 2.2 Positive density is unconditional

**Proposition D.** `G` has a natural density, equal to `(1/8)∏_{ℓ≡1 (4)}(1 − 2/(ℓ − 1)²)`; in
particular its relative lower density in the primes is positive.

*Proof sketch.* For a cutoff `L`, let `G_L` be the primes of the class with no bad `ℓ ≤ L`. Bad
events at `ℓ ≤ L` are conditions on `π` modulo `m_L = ∏_{ℓ≤L} ℓ`, together with conditions modulo
`8` and `7` on `p = ππ̄`; Hecke's prime ideal theorem for the ray class groups of `ℚ(i)` (STANDARD,
e.g. Narkiewicz, *Elementary and analytic theory of algebraic numbers*, Ch. 7; Neukirch, *ANT*
VII.13) gives `G_L` the density `(1/8)∏_{ℓ≤L, ℓ≡1 (4)}(1 − 2/(ℓ − 1)²)`. The primes of `G_L` that
are bad at some `ℓ > L` number `≪ N/(L log N) + N^{7/8}` up to `N`: for `L < ℓ ≤ N^{1/8}`, an upper
bound sieve on the lattice `a ≡ 0`, `b ≡ b₀ (mod ℓ)` gives `≪ N/(ℓ² log N)`; for larger `ℓ`, the
lattice count gives `≪ N/ℓ² + √N/ℓ`. This is the manuscript's computation at lines 1600–1642, with
"the prime value of a fixed form" replaced by "a prime up to `N`". Letting `L → ∞` gives the
density. ∎ (SPECULATIVE only in that it is a transposition of the manuscript's argument, not
written out; each step is STANDARD or elementary.)

Hecke's theorem can be avoided at the price of the exact constant. The congruences `p ≢ −1
(mod ℓ)` for odd `ℓ ≤ L` are conditions on `p` alone. Imposing them leaves relative density
`≫ 1/log L` by the prime number theorem in arithmetic progressions, against a tail `O(1/L)`. This
is exactly the manuscript's choice (lines 1384–1390 and the classes `c_q`, lines 1332–1335). It
gives positive lower density with only the rational prime number theorem in progressions and the
elementary sieve.

This is the CM analogue of Serre's cyclicity problem, which is known unconditionally for CM curves
(R. Murty, 1983; Cojocaru, 2003) because the bad events at `ℓ` have density `≍ 1/ℓ²` and can be
counted in the Gaussian lattice. For non-CM curves the same statement needs GRH. UNCHECKED (the
two papers could not be read; the attribution is from memory). The point used here, the
lattice-sieve argument, is in the manuscript itself.

### 2.3 How the manuscript obtains its good primes

In the proof of Proposition 6.2 (lines 1291–1704) the gcd condition is handled in three places:

1. **Small `ℓ` by congruences.** The prescribed residues `c_2 = 1 (8)`, `c_7 = 3 (7)`,
   `c_q = 1 (q)` for the other `q ≤ 324` (lines 1332–1335), the catalogue residues `≠ 0, −1`
   (lines 1351–1354), and the exclusion of the planes `ε_νF_ν = −k_ν` at every `q ≤ L` (lines
   1384–1390) make every prime value `p ≢ −1 (mod ℓ)` for each odd `ℓ ≤ L`. VERIFIED.
2. **The CM identities** (lines 1554–1598, record A072, Silverman III.7.4, III.8.6, V.1.1,
   V.2.3.1): the description of §2.1. VERIFIED by reading and by the computation above.
3. **Large `ℓ` by a lattice sieve** (lines 1600–1642): the number of bad prime values of a fixed
   form is `≪_A X/(L log X) + X^{7/8} + √X log X`, uniformly in `L` (equation
   `prime-bad-values`); multiplied by the fiber bound (lines 1644–1680) and compared with the lower
   count, it is absorbed by choosing `L` before `X` (lines 1682–1704).

The argument is unconditional and, as far as I can check it, complete; it uses only the
Green–Tao asymptotic (record A021) for the lower count and elementary sieves for the rest. It
does not need GRH, Chebotarev with error terms, or any non-CM input. **Finding: no defect.**

### 2.4 Where the gcd condition is used, and why finitely many conditions do not serve the test

**Uses** (VERIFIED, by reading the Lean consumers):

- `GoodSlopePrime` enters the completeness proof only through `GoodSlope.contact`, destructured in
  `slope_complete` (`SlopeCompleteness.lean`, `obtain ⟨-, hgood, -⟩ := ht.contact …`) and passed to
  `exists_shift` (`SlopeCompleteness.lean:47–66`).
- `exists_shift` uses the root `r` of `X² − 2`, the two non-vanishing conditions `75 ∓ 53r ≠ 0`,
  and `gcd(d₁, d₂) = 4`. The last is used only by `shift_choice'` (`ShiftChoice.lean`), which
  solves `h ≡ 0 (mod lcm(M₀, d₁))`, `h ≡ c_* (mod d₂)`.
- `tests_precision_selected` then needs only `d₁ | h` and `d₂ | h − c_*` (and `324 < p`).
- Manuscript: the same, lines 1706–1716 ("Compatibility follows from
  `gcd(lcm(M₀, d₁), d₂) | M₀ gcd(d₁, d₂) = 4M₀ = c_*`").

So the only consumer is the Chinese remainder step for the shift `h` of the group assigned to the
prime. As [RP §1.4] notes, the step needs only `gcd(e₁, e₂) | c_*` for the orders `e₁, e₂` of `P₀`
at the two places above `p`, a one-lemma relaxation.

**Necessity.** The honest witnesses of the group assigned to `p` must put `H` in the formal group at
one place above `p`, and `H − [c_*]P₀` at the other (lines 1196–1199, 1706–1712). For `H ∈ E(K₀)`
the odd parts of these two conditions are `h ≡ 0 (mod e₁′)` and `h ≡ c_* (mod e₂′)`, where `e₁′`,
`e₂′` are the odd parts of the reduction orders. They are compatible iff the odd part of
`gcd(e₁, e₂)` divides `c_*`. Torsion in `E(K₀)` changes only 2-parts. So some condition at every
odd `ℓ ∤ c_*` is necessary for the group at `p` to succeed: a slope with an odd contact prime `p`
for which `ℓ | gcd(e₁, e₂)`, `ℓ ∤ c_*`, cannot pass the slope predicate with that prime selected.
VERIFIED, as an argument from the test identities; [RG F4] explains why the shift must be fixed.

**No finite version.** The bad events at different `ℓ` are independent: they are conditions on
`π` modulo coprime moduli, and Hecke's theorem equidistributes Gaussian primes in
`(ℤ[i]/m)^×`. So for any finite set of `ℓ` and any admissible class, a positive proportion of the
primes in it are bad at some further `ℓ`; no Chebotarev condition in one fixed number field implies
`gcd(d₁, d₂) = 4`. VERIFIED for `d₁, d₂` from the CM description. For the orders `e₁, e₂` of `P₀`,
the corresponding statement needs the Kummer theory of `P₀` and is SPECULATIVE. A finite version
would therefore serve the multiplication completeness proof only after a change of the test, and
[RG F4, A7, A8] show that the fixed shift cannot be removed.

**Why it does not matter.** Every route to the pattern considered here (the manuscript's GTZ
argument and the Green–Tao 2008 route of §3) needs good primes only through counting:

- the GTZ route needs an upper bound for bad primes in a pattern, which the CM lattice sieve gives;
- the Green–Tao 2008 route needs positive relative upper density of `G`, which Proposition D gives.

The infinite family of conditions is thus elementary bookkeeping, not a source of depth. The
relaxation `gcd(e₁, e₂) | c_*`, or a larger shift [RG A8], raises the density but changes nothing
qualitative.

---

## 3. Green–Tao 2008 suffices (question 2)

### 3.1 The obstacle of route R4

Green–Tao 2008 (*The primes contain arbitrarily long arithmetic progressions*, Ann. of Math. 167
(2008) 481–547, Theorem 1.2): every subset of the primes of positive relative upper density contains
arithmetic progressions of every finite length. STANDARD; the statement is quoted from memory and
agrees with the arXiv abstract (math/0404188: the transference principle gives progressions in "any
subset of a sufficiently pseudorandom set of positive relative density"); the theorem number is
UNCHECKED. A `(K + 1)`-term progression `x, x + v, …, x + Kv` contains the homothetic copy
`{x + jv : j ∈ J}` of every `J ⊂ [0, K]`. So Green–Tao 2008 applied to `G` produces the twelve
primes of 22P₂, but with no control of the common difference `v`.

22P₂ asks for `v_q(v) ≤ 4` at `q ≤ 324` (and `≤ 1` at the catalogue). [RP §2.3, R4] argues that
this is unavoidable ("an unbounded `v_q(t)` at an old prime makes `v_q(RC²)` for `k = 25` tend to
`−∞`; the fixed `ℓ₀` and `c_*` cannot compensate"). It also notes, correctly, that no Szemerédi-type
theorem forces valuation conditions on the difference for general dense subsets of the primes. For
example, inside the primes `≡ 1 (mod 3⁵)` every difference is divisible by `3⁵`. The literature
search of §3.5 found nothing that gives the condition for the primes. The argument of [RP] overlooks
one free parameter: the witness `q`.

### 3.2 Poles at old primes are absorbed by the witness `q`

**Lemma P (pole absorption).** Let `ℓ` be a prime, `t = u/v ∈ ℚ` in lowest terms with
`e = v_ℓ(v) ≥ 1`, and assume that the seven numbers `u − cv` (`c ∈ 𝒞`) and `u − v` are prime to
`ℓ`, and that `F(t) > 0` (so `η = 1`). Assume `ℓ` odd, or `ℓ = 2` and `e ≥ 3`.

1. `v_ℓ(R₀) = 2e`, `v_ℓ(t − 1) = −e`, and `R₀` is a square in `ℚ_ℓ`.
2. For every `N` the set of `q ∈ ℚ_ℓ` with `v_ℓ(1 − R₀q²) ≥ N` is a non-empty open set.
3. Suppose that at every place `𝔩` of `K₀` above `ℓ` all test values satisfy `v_𝔩(D_{gj}) ≥ 0`, with
   `v_𝔩` normalized to extend `v_ℓ`. If `v_ℓ(a) ≥ N ≥ 23e + v_ℓ(12) + 2`, then `v_ℓ(B) ≥ 4`.

*Proof.* (1) `R₀ = F(t)/(t − 1)⁸ = v²F(u, v)/(u − v)⁸`, and
`F(u, v) = u⁶∏_{c∈𝒞}(1 − cv/u)` with `u` an `ℓ`-unit (it is the value `u − 0·v`). Hence
`R₀ ℓ^{−2e} = (vℓ^{−e})² u⁶ (u − v)^{−8} · ∏_c(1 − cv/u)`. The first three factors are squares of
`ℓ`-units, and the product is `≡ 1 (mod ℓ^e)`. A unit `≡ 1 (mod ℓ)` is a square in `ℚ_ℓ` for odd
`ℓ`, and a unit `≡ 1 (mod 8)` is a square in `ℚ₂`.

(2) Take `q₀ = ±R₀^{−1/2} ∈ ℚ_ℓ`. Then `1 − R₀q² = −R₀(q − q₀)(q + q₀)`, and
`v_ℓ(1 − R₀q²) = 2e + v_ℓ(q − q₀) + v_ℓ(q + q₀) ≥ N` on a small ball around `q₀`.

(3) Write `E_ℓ = v_ℓ(ℓ₀) ≥ 0` and `α = v_ℓ(a)`. Then `v(R) = 2E_ℓ + 2α + 2e`, and
`v(C_{gj}) = v(D_{gj}) − 2ek_j + e(k_j + 1) ≥ −e(k_j − 1)`, so
`v(RC_{gj}²) ≥ 2E_ℓ + 2α + 2e − 2e(k_j − 1) ≥ 2α − 46e` for `k_j ∈ {1, 25}`. With `α ≥ N` this
exceeds `v_ℓ(12)`. Each `W_g` is then `≡ 1` to valuation `> v_ℓ(12)` at every place above `ℓ`, so
`Θ = 12 + Tr Σ_g (W_g^{−1} − 1)` has `v_ℓ(Θ − 12) > v_ℓ(12)` and `v_ℓ(Θ) = v_ℓ(12)`. Finally
`v_ℓ(B) = v(R) − 2v_ℓ(12) ≥ 2N − 2v_ℓ(12) ≥ 4`. ∎ VERIFIED (by hand, above).

The hypothesis of (3) holds at every `ℓ ∈ S_b` for the honest witnesses, since `M₀ | h`
(`ZInQ.Mult.tests_integral_old`, `SbIntegrality.lean:98`, whose hypotheses do not mention `t`;
manuscript line 1728). The same computation is the manuscript's real-place argument (`a → 0`,
lines 1747–1751), transported to `ℚ_ℓ`; it needs `R₀` to be a local square, as the real argument
needs `R₀ > 0`.

**Numerical check** (`scratch/nt-22p/atrick.py`, 30 random samples with `v_ℓ(v)` up to 40 at each
`ℓ ∈ S₀`):

- `R₀` was a square in `ℚ_ℓ` at all five primes in 30 of 30 samples;
- one rational `q` was built for each sample by the Chinese remainder theorem with an auxiliary
  prime, as in `ZInQ.Mult.weak_approx_q`. In all 30 samples it had `v_ℓ(a) ≥ 25v_ℓ(v) + 10` at all
  five primes and `|a| < 10^{−300}`.
- Control: with `v₂(v) ≤ 2`, `R₀` is often not a square in `ℚ₂` (22 non-squares among the valid
  samples). This is why Lemma P assumes `e ≥ 3` at 2; for `e ≤ 2 ≤ B₂` the existing argument
  applies.

VERIFIED (computation).

**The modified completeness argument.** Replace field 2 (`old`) of `GoodSlope` by:

> **2′.** For every `ℓ ∈ S_b`, either the bounds of field 2 hold at `ℓ`, or `F(t) > 0` and `t`
> satisfies the hypotheses of Lemma P at `ℓ`.

In the proof of slope completeness (manuscript lines 1720–1758; Lean `slope_complete`,
`pole_input_valuations`, `weak_approx_q`), let `S_pole ⊂ S_b` be the primes where the second
alternative is used. Choose `q` by weak approximation as now, except that at `ℓ ∈ S_pole` it lies in
the ball of Lemma P(2) with `N = 23v_ℓ(v) + v_ℓ(12) + 2`, instead of `v_ℓ(q) ≥ C_ℓ`.

- At `ℓ ∈ S_pole`, Lemma P(3) gives `v_ℓ(B) ≥ 4`.
- At the other primes of `S_b` the old argument applies unchanged.
- At the selected odd contact primes, `q` is still integral, so `a` is a unit and `v_p(B) = 1`.
- At all other primes, `a` contributes an even valuation, so the parity argument is unchanged.
- At the real place, `a → 0` as before.

The polynomial, the slope predicate and soundness are untouched: `a` enters `R` squared (line
1180), so it never changes the parity of a valuation. SPECULATIVE only in that the modified proof
has not been written out in Lean; every step is the existing one or Lemma P.

### 3.3 The progression form of the hypothesis

Put `A′ = A + 10`, `T = 𝒞 ∪ {1}` and `S_A⁺ = T ∪ (A′ − T)`, a set of at most 14 integers, and let
`K_A = max S_A⁺ − min S_A⁺`. Let `G′ = {p ∈ G : p > max(S_b)}`.

> **22P_AP.** For every `K` the set `G′` contains an arithmetic progression
> `x, x + v, …, x + Kv` with `x ≥ 1` and `v ≥ 1`.

This statement does not mention `A`, the catalogue multipliers or the old primes, except through
the lower bound `max S_b` for the primes.

**Proposition AP.** 22P_AP implies the slope representation (with field 2 replaced by 2′, §3.2).

*Proof.* Given `A`, take a progression of length `K_A + 1` in `G′` and put
`u = x + (max S_A⁺)v`. For `c′ ∈ S_A⁺` the number `u − c′v = x + (max S_A⁺ − c′)v` is a term of
the progression, so all fourteen numbers `u − c′v` are primes of `G′`. Put
`t₁ = u/v`, `t₂ = A′ − u/v`, `t₃ = −10`.

- *Lowest terms.* A prime dividing `u` and `v` divides every term, which are distinct primes:
  impossible. So `t₁ = u/v` and `t₂ = (A′v − u)/v` are in lowest terms.
- *Field 1.* `u − cv ≠ 0` and `u − v ≠ 0`, hence `t₁ ∉ 𝒞 ∪ {1}`; the same for `t₂`, whose numbers
  `t₂ − c = −(u − (A′ − c)v)/v` and `t₂ − 1 = −(u − (A′ − 1)v)/v` are nonzero.
- *Signs.* `t₁ = max S_A⁺ + x/v > max S_A⁺ ≥ 1 > 0`, so `F(t₁) > 0`. Also
  `t₂ = A′ − max S_A⁺ − x/v`. If `A′ + 60 ≥ 1` then `max S_A⁺ = A′ + 60` and `t₂ < −60`; otherwise
  `max S_A⁺ = 1` and `t₂ < A′ − 1 < −60`. In both cases all six factors `t₂ − c` are negative and
  `F(t₂) > 0`. So `η = 1` for both slopes, as Lemma P requires. This needs no condition on the
  progression.
- *Field 2′ at `ℓ ∈ S_b`.* All fourteen numbers are primes larger than `max S_b`, so they are
  `ℓ`-units. Let `e = v_ℓ(v)`.
  - If `e = 0`, then `v_ℓ(t − 1) = 0` and `v_ℓ(F(t)/(t − 1)⁸) = 0`, and field 2 holds.
  - If `e ≥ 1`, then `v_ℓ(t − 1) = −e` and `v_ℓ(F(t)/(t − 1)⁸) = 2e`. Field 2 holds when
    `e ≤ B_ℓ`. Otherwise `e ≥ 2` (since `B_ℓ ≥ 1`) and, for `ℓ = 2`, `e ≥ 5 > 3`. The hypotheses
    of Lemma P hold: the seven numerators are units and `F(t) > 0`.
- *Fields 3 and 4.* For `j = 1, 2` the odd contact primes of `t_j` outside `S_b` are exactly the six
  primes `u − cv` (for `t₁`) or `u − (A′ − c)v` (for `t₂`), each with contact valuation 1. Primes
  dividing `v` give negative valuations, and a pattern prime does not divide `v`. This is the
  argument of `Mult.slopeRepresentation_of_twoSlopePattern` (`TwoSlope.lean`), unchanged.
- *The constant slope.* `GoodSlope 0 (−10)` holds with no contact prime outside `S_ht`
  ([RP §2.5], VERIFIED there by computation).

So `A = t₁ + t₂ + t₃` with three good slopes in the sense of 2′. ∎ VERIFIED (by hand), given
Lemma P. Strictly, a progression of length `K_A + 1` is more than needed (only the fourteen terms
indexed by `max S_A⁺ − S_A⁺` are used), but it is what Green–Tao 2008 provides.

Two remarks.

1. Field 2′ is not a weakening one can avoid by a clever choice of progression: every progression of
   `K + 1` primes larger than `K + 1` has `v` divisible by every prime `≤ K + 1`, and `K_A ≈ |A| + 71`.
   So for large `|A|` every old prime divides `v`, usually to a high power. This is the obstacle of
   [RP R4], and Lemma P is what removes it. VERIFIED (elementary: if `ℓ ≤ K + 1` and `ℓ ∤ v`, the
   terms run through all classes mod `ℓ`).
2. The numbers `u − v` and `u − (A′ − 1)v` are prime in this form only for convenience. They make
   field 2 trivial at the old primes not dividing `v`. Without them one needs
   `v_ℓ(u − v) ≤ B_ℓ` there, which is again a restriction that no Szemerédi-type theorem provides.
   Including two more points in the pattern costs nothing.
3. Pole completeness asks for `v_ℓ(B) ≥ 4` only at `ℓ ∈ S₀ = {2, 3, 5, 7, 13}` (§1). At an old
   prime `ℓ ∈ S_b ∖ S₀` it asks only that a negative valuation of `B` be even. In the progression form
   the numerators are `ℓ`-units, so `v_ℓ(R₀) = 2v_ℓ(v)` is even, and `v_ℓ(B) = v_ℓ(R) − 2v_ℓ(Θ)` is
   even whatever `q` is. So Lemma P is needed only at the five primes of `S₀`. Field 2′ is stated for
   all of `S_b` only to keep the existing proof structure. VERIFIED (by hand, from `R = ℓ₀²a²R₀`).

### 3.4 Green–Tao 2008 implies 22P_AP

**Theorem** (Green–Tao, *The primes contain arbitrarily long arithmetic progressions*, Ann. of
Math. 167 (2008), 481–547, Theorem 1.2, "Szemerédi's theorem in the primes"). *Let `A` be a subset
of the primes with `limsup_{N→∞} π(N)^{−1}|A ∩ [1, N]| > 0`. Then `A` contains infinitely many
arithmetic progressions of length `k`, for every `k`.* STANDARD; statement VERIFIED against the
arXiv TeX source math/0404188v6 (theorem `sz-primes`, the second theorem of §1).

Apply it to `G′`. By Proposition D, `G′` has relative density about `0.106 > 0` (removing finitely
many primes changes nothing). A progression of primes with `k ≥ 2` terms has `v ≠ 0`. Reversing the
order if necessary, `v ≥ 1`. So 22P_AP follows. VERIFIED, given Proposition D.

**What the proof of the main theorem then rests on, for this hypothesis:**

| Input | Status | Where |
| --- | --- | --- |
| Green–Tao 2008, Theorem 1.2 | STANDARD | §3.4 |
| CM identities for the reductions of `E` (Silverman III.7.4, III.8.6, V.1.1, V.2.3.1) | STANDARD, record A072 | §2.1; needed only to identify `G` |
| PNT in progressions (fixed modulus), or Hecke for `ℚ(i)` for the exact constant | STANDARD | Proposition D |
| Lattice sieve for the bad `ℓ > L` | elementary (manuscript lines 1600–1642) | Proposition D |
| Lemma P and the modified choice of `q` | elementary, VERIFIED by hand | §3.2 |
| Proposition AP | elementary, VERIFIED by hand | §3.3 |

Compared with the manuscript's proof of Proposition 6.2 (record A021: Green–Tao 2010 linear
equations, Green–Tao 2012 Möbius–nilsequences, Green–Tao–Ziegler 2012 inverse theorem), the
following leave: the inverse theorem for all Gowers norms, the Möbius–nilsequence estimate, the
singular-series analysis (lines 1382–1453), the two-variable Selberg sieve with uniform constants
(1455–1552) and the fibre count (1644–1680). The catalogue `𝓗` also loses its role in the proof
of the pattern ([RP R2]), since no unit classes need adjusting.

Green–Tao 2008 itself uses Szemerédi's theorem (in its quantitative finite form), the transference
principle and the Goldston–Yıldırım correlation estimates. Conlon, Fox and Zhao
(*A relative Szemerédi theorem*, GAFA 25 (2015); arXiv:1305.5440; and the exposition
arXiv:1403.2957) simplified the transference so that only a linear forms condition on the majorant
is needed, and the correlation condition disappears (STANDARD as described in the abstracts;
UNCHECKED in detail). This is the shortest known route, and the one a formalization would follow.

### 3.5 Literature on restricted common differences

Before Lemma P removed the need, I looked for Szemerédi-type theorems in the primes in which the
common difference has prescribed valuations at finitely many primes (only arXiv abstracts and
sources were readable):

- Tao–Ziegler, *The primes contain arbitrarily long polynomial progressions* (Acta Math. 201 (2008);
  arXiv:math/0610050): `x + P_i(m)` prime for integer polynomials with `P_i(0) = 0` and
  `1 ≤ m ≤ x^ε`. Taking `P_i(m) = i·Wm` forces divisibility of the difference by `W`, which is the
  opposite of what was needed. No valuation upper bound.
- Bergelson–Leibman–Ziegler (arXiv:1007.1839) and related work on differences from the shifted
  primes `p − 1`: ergodic statements for dense subsets of the integers, not of the primes.
- Frei–König–Tinková, *Linear constellations in primes with arithmetic restrictions*
  (arXiv:2408.17441): the Green–Tao linear-equations asymptotic for primes with prescribed Artin
  symbols, unconditionally. It covers the Chebotarev part of goodness, not the gcd condition, and it
  rests on the Green–Tao–Ziegler machinery, so it does not lower the depth.
- Narrow progressions (arXiv:1409.1327, 1509.04955): progressions with small difference, not
  difference in a prescribed class.

No theorem with valuation-restricted differences for dense subsets of the primes was found. One
cannot hold in general: inside the primes `≡ 1 (mod 3⁵)` every difference is divisible by `3⁵`. A
`W`-trick does not help either. It changes the dense set at each term of the progression, which the
relative Szemerédi theorem does not handle ([RP R4]). The question is moot after Lemma P.

---

## 4. Can fewer forms be prime at once? (question 3)

[RP §2.3, R3, R6, R8] argues that two non-constant slopes with twelve prime forms are forced. This
section tests that argument piece by piece. The conclusion is that it is right for every
construction in which the slopes are linear fractional functions of the parameters. The twelve forms
can, however, be put in one arithmetic progression (§3.3), and that is what matters for the depth.

### 4.1 One slope already needs six prime forms

Let `t = u/v` be a good slope (fields 1–4), and `P` its set of odd contact primes outside `S_b`.
Call a contact value `u − cv` *square-like* if it has no prime outside `S_b` to an odd power.

- *Each value that is not square-like carries exactly one prime of `P`.* For `p > 324` at most one
  contact value is divisible by `p`: a common prime of `u − cv` and `u − c′v` divides `(c − c′)v`,
  hence `c − c′` (it cannot divide `v` and `u`), and `|c − c′| ≤ 60`. So the primes of `P` are distributed over the six values,
  and `|P| ≤ 6` (field 4). If all six values fail to be square-like, each carries exactly one prime
  of `P` to an odd power (`= 1`, field 3), times an `S_b`-part and a square. VERIFIED (elementary).
- *Square-like values cut out curves of positive genus.* Requiring `m` of the six values to be
  `S_b`-units times squares puts `(u : v)` on one of finitely many `(ℤ/2)^{m−1}`-covers of `ℙ¹`
  branched at `m` points, of genus `1 + 2^{m−3}(m − 4)`: genus 0 for `m ≤ 3`, 1 for `m = 4`, 5 for
  `m = 5`, 17 for `m = 6` ([RP R6], STANDARD by Riemann–Hurwitz). For `m ≥ 5` there are finitely many
  points (Faltings). For `m = 4` the points lie on finitely many elliptic curves, and the remaining two
  values would be two functions on an elliptic curve required to be prime at once: no theorem of
  that kind exists. For `m = 3` the conic is rational, but `u` and `v` become binary quartic forms in
  the new parameters, and three binary quartics would have to take prime values at once. Prime values
  of a single general binary quartic are not known (Heath-Brown handled `x³ + 2y³`;
  Friedlander–Iwaniec handled `x² + y⁴`).

So in any family that is linear in the parameters, a slope of unbounded height needs all six
contact values prime (up to bounded factors). VERIFIED in the sense just stated. A
construction with nonlinear forms only makes the prime problem harder.

*Complexity.* The six forms `u − cv`, `c ∈ 𝒞`, are pairwise independent linear forms in two
variables. Their true complexity in the sense of Green–Tao (*Linear equations in primes*, Ann. of
Math. 171 (2010), §1, and Gowers–Wolf) is the least `s` for which the powers `(u − cv)^{s+1}` are
linearly independent. These are six binary forms of degree `s + 1`, in a space of dimension `s + 2`,
and by Vandermonde they are independent as soon as `s + 2 ≥ 6`. So the true complexity is 4. STANDARD definition; the
computation is VERIFIED (elementary). The circle method controls systems of true complexity 1
(three-term progressions: van der Corput 1939; Green, Ann. of Math. 161 (2005) for dense subsets).
So even one good slope of large height is beyond Fourier analysis. The answer to "at most three
forms" is no.

### 4.2 Two non-constant slopes are forced

The manuscript writes each integer as a sum of three slopes. Could all but one of them be constants?

Let `T₀` be the set of good slopes with no odd contact prime outside `S_b`. For `t = u/v ∈ T₀`,
`F(u, v) = Dm²` with `D` a signed product of primes of `S_b`. So `(u/v, m/v³)` is a rational point on
one of finitely many genus-2 curves `Dy² = F(x)`. By Faltings's theorem (STANDARD), `T₀` is finite.

**Claim.** If `K ⊂ ℚ` is finite, the integers `A` for which some `k ∈ K` makes `A − k` a good slope
miss a set of positive density.

*Proof.* For each `k = r/s ∈ K` choose a distinct prime `p_k ∤ s` outside `S_b` with `p_k ≡ 3 (mod 4)`
(such a prime is never good, §2.1). By the Chinese remainder theorem, the integers `A` with
`v_{p_k}(sA − r) = 1` for every `k` form a set of density `∏_k (p_k − 1)/p_k² > 0`. For such `A`
the slope `A − k` has the odd contact prime `p_k` at the contact `c = 0`, and `p_k` is not good. ∎
VERIFIED (elementary). With `K = T₀ + T₀` this rules out "one variable slope plus two constant
slopes": a positive density of integers is missed. The two-slope form 22P₂ therefore uses the minimum,
two variable slopes (which share their denominator and so cooperate) and one constant.

Numerically the obstruction appears late (`scratch/nt-22p/constslopes.py`, PARI/GP):

| Quantity | Value |
| --- | --- |
| smooth good slopes `u/v` with `|u|, v ≤ 120` (`S_b = S_ht`) | 3,670 |
| `|T₀ + T₀|` within that box | 3,771,642 |
| integers `0 ≤ |A| < 3000` of the form `k₁ + k₂ + t`, `kᵢ` smooth, `t` good | all 6,000 |

VERIFIED (computation). So small `A` are easy. The Claim shows the failure is real but begins only
at large `A`, as the size of `T₀` suggests. The constant slope `−10` is useful precisely because it
lets the two variable slopes share one denominator.

### 4.3 Three slopes do not help, and two slopes give a progression

- With three variable slopes `t_j = u_j/v` and `Σu_j = Av`, the eighteen contact forms live in three
  variables and are not translation-invariant ([RP R3]: the coefficient `1 + σ₂ + σ₃` of `u₁`
  cannot vanish). They are not a homothetic copy of a fixed set, so Green–Tao 2008 does not apply.
- With slopes with different denominators `u/v + u′/v′ = A′`, the condition is quadratic.
- With a common denominator and two slopes, the forms are `u − c′v`, `c′ ∈ S_A⁺`, a homothetic copy
  of a 14-point set of integers, hence contained in one progression (§3.3). This is the cheapest
  shape the architecture allows. Its depth is that of Szemerédi's theorem in the primes, and
  Green–Tao 2008 supplies it.

### 4.4 The symmetry of the contact set

The Möbius transformations of `ℙ¹(ℚ)` mapping `𝒞` onto itself form a group of order 12
(`scratch/nt-22p/mobius.py`: twelve maps, among them a 6-cycle
`0 → −15 → −20 → −24 → −30 → −60 → 0`; so the group is dihedral of order 12 and `𝒞` is the vertex
set of a "hexagon" on the conic `ℙ¹`). VERIFIED (computation). For `γ` in this group,
`γ(t) − γ(c) = det(γ)(t − c)/(j(t)j(c))` with `j` the denominator of `γ`, so `t` and `γ(t)` have the
same odd contact primes outside the primes of `det γ` and of the coefficients. Goodness is therefore
preserved up to the old primes, but `γ` does not fix the sum condition `t₁ + t₂ = A′`. It produces
more good slopes from one good slope, not fewer prime forms. SPECULATIVE beyond this: I see no use
of the symmetry for the pattern.

---

## 5. Ranking of routes

| Rank | Route | Payoff | Main obstacle | Chance |
| --- | --- | --- | --- | --- |
| 1 | **AP**: Lemma P + field 2′ + hypothesis 22P_AP (§3.2–3.3) | 22P becomes "the good primes contain arbitrarily long progressions", independent of `A`; its proof needs only Green–Tao 2008 | Lean work: field 2′, a local square root, a weak approximation with residue targets | high |
| 2 | **D**: write out Proposition D | the justification of 22P_AP becomes GT08 Thm 1.2 plus textbook inputs | a careful write-up of the CM lattice sieve with uniform constants | high |
| 3 | **R**: relax `gcd(d₁, d₂) = 4` to `gcd(e₁, e₂) | c_*` | in-class density 0.85 → 0.88; a cleaner `GoodSlopePrime` | none (one lemma in `shift_choice`), but almost no payoff | high (low value) |
| 4 | **F**: a goodness condition with finitely many Chebotarev conditions | would make `G` a Chebotarev set | impossible for the fixed-shift test (§2.4); needs a new test, against [RG F4, A8] | low |
| 5 | **C**: at most three simultaneous prime forms (circle method) | would remove Szemerédi-type input | each slope needs six forms of true complexity 4 (§4.1) | negligible |

**Route 1 (AP).**
- *Payoff.* The Lean hypothesis `TwoSlopePattern` (twelve values, valuation side conditions, `A`
  quantified) is replaced by
  `GoodPrimeAP : ∀ K N : ℕ, ∃ x v : ℕ, N < x ∧ 0 < v ∧ ∀ j ≤ K, GoodSlopePrime (x + j * v)`.
  This is literally a special case of Green–Tao 2008 Theorem 1.2 once `G` has positive relative
  density. The GTZ machinery of record A021 leaves the trust base of this hypothesis.
- *Main obstacle.* Three Lean changes:
  - `GoodSlope.old` becomes the disjunction 2′;
  - `slope_complete`/`pole_input_valuations` gain the Lemma P branch at old primes. The algebra is
    the existing `S_b` estimate with `v(R) ≥ 2N` in place of `v(ℓ₀)`;
  - `weak_approx_q` (`WeakApproximation.lean:29`) must hit a residue class `q ≡ q_ℓ (mod ℓ^{N})`
    after scaling by `ℓ^{e}`, not only `v_ℓ(q) ≥ e_ℓ`. The class is an integer square root of the unit
    `(R₀ℓ^{−2e})^{−1}` modulo `ℓ^{N}`, obtained by Hensel lifting (Mathlib has Hensel's lemma for `ℤ_[p]`
    and `ZMod` square roots). The grid argument of `weak_approx_q` adapts by shifting the grid.
- *First test.* State and prove in Lean the integer form of Lemma P(1)–(2): for `ℓ` odd (or `ℓ = 2`,
  `e ≥ 3`), `u, v` as in Lemma P and every `N`, there is `w ∈ ℤ` with
  `v_ℓ(1 − (R₀ℓ^{−2e})w²) ≥ N` (then `q = w/ℓ^{e}` has `v_ℓ(1 − R₀q²) ≥ N`). Then derive `SlopeRepresentation'` from `GoodPrimeAP` along §3.3.
  *Success criterion:* `Mult.slopeRepresentation_of_goodPrimeAP` builds, and the main theorem
  builds with `GoodPrimeAP` in place of `TwoSlopePattern`, axioms unchanged.
- *Chance: high.* Every step is elementary and checked by hand. Lemma P was tested on 30 samples
  (§3.2). The sign condition is automatic (§3.3). The main risk is Lean effort, not mathematics.

**Route 2 (D).**
- *Payoff.* A complete proof that `G` has positive relative lower density, from the prime number
  theorem in progressions, the CM identities (A072) and an elementary lattice sieve. With Route 1 this makes
  22P a corollary of a single classical theorem (GT08).
- *Main obstacle.* Uniformity of the sieve bound for `L < ℓ ≤ N^{1/8}` (a Selberg or Brun upper
  bound for primes in a lattice of index `ℓ²` in `ℤ[i]`), and the CM identification written for `p`
  rather than for a value of a form. Both are in the manuscript (lines 1554–1642) in a slightly
  different setting.
- *First test.* Write the proof with explicit constants and check it numerically. For `L = 50` the
  predicted lower bound for the relative density of `G` must lie below the observed `0.1064`
  (`scratch/nt-22p/density.py`) and be positive.
- *Chance: high*, because the manuscript's argument transposes directly.

**Route 3 (R).** *Payoff* small. *Obstacle* none. *First test:* change `shift_choice'` to assume
`gcd(d₁, d₂) ∣ c_*`; success if `exists_shift` still builds. *Chance high, value low.* It does not
change the depth of anything.

**Route 4 (F).** *Payoff:* `G` would become a Chebotarev set. *Obstacle:* the honest witnesses need
the odd part of `gcd(e₁, e₂)` to divide `c_*` (§2.4). A test with a finite set of shifts absorbs only
finitely many `ℓ`, and a witness shift is circular [RP R8]. *First test:* exhibit a test with
fixed shifts `c₁, …, c_r` whose success condition at `p` is a Chebotarev condition in one fixed
field; success if the condition is implied by a Frobenius class in a fixed finite extension.
*Chance low*: under Route 1 only positive density is needed, so this would buy nothing anyway.

**Route 5 (C).** *Payoff:* replace Szemerédi-type input by Fourier analysis. *Obstacle:* §4.1
(true complexity 4 per slope; square-like values lead to curves of positive genus or to binary
quartics). *First test:* none sensible. *Chance negligible* in the present architecture: a
different height theorem with at most three contacts is impossible ([RP R8], positive-rank
twists of elliptic curves).

**Recommendation.** Take Route 1 together with Route 2. The prime-pattern hypothesis then becomes the
single statement that the good slope primes contain arbitrarily long arithmetic progressions. That
is an immediate corollary of Green–Tao 2008 and of an elementary density computation for a CM
curve. The construction (the polynomial) does not change; only the completeness proof uses the
witness `q` more cleverly at the old primes.
