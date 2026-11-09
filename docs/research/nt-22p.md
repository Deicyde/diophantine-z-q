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
one place above `p`, and `H − [c_*]P₀` at the other (lines 1185–1190, 1706–1712). For `H ∈ E(K₀)`
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
