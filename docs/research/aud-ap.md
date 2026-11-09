# Audit of the progression variant of the main theorem: the statements

Subject: the Lean theorem `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP`
(`ZInQKernel/Main.lean`), its new hypothesis `ZInQ.GoodPrimeAP`
(`ZInQKernel/Hypotheses/PrimeAP.lean`) and the definitions of the new modules
`ZInQKernel/Multiplication/Completeness/AP/*.lean`, compared with `docs/research/nt-22p.md` §3
(Lemma P, field 2′, the hypothesis 22P_AP, Proposition AP), with the referee reports
`rv-nt22p-proof.md` and `rv-nt22p-ap.md`, and with Green–Tao 2008, Theorem 1.2. The kernel checks
the proofs; this audit concerns what the statements say.

Each examined step is marked CORRECT (checked here), GAP (missing or wrong) or UNCHECKED.

<!-- VERDICT -->

## 1. The hypothesis `GoodPrimeAP`

### 1.1 The Lean statement

```lean
def GoodPrimeAP : Prop :=
  ∀ K : ℕ, ∃ x v : ℕ, 1 ≤ x ∧ 1 ≤ v ∧
    ∀ j ≤ K, GoodSlopePrime (x + j * v) ∧ ∀ q ∈ Mult.S_b, q < x + j * v
```

with

- `GoodSlopePrime p := p.Prime ∧ ∃ r : ZMod p, r² = 2 ∧ 75 − 53r ≠ 0 ∧ 75 + 53r ≠ 0 ∧
  gcd(#E_r(𝔽_p), #E_{−r}(𝔽_p)) = 4`, where `#E_r(𝔽_p)` (`pointCount p (−(75 − 53r)²)`) is the
  number of affine solutions of `y² = x³ − (75 − 53r)²x` over `ZMod p`, plus one;
- `Mult.S_b = S_ht ∪ catalogue`, with `S_ht = {p prime : p ≤ 324}` (a filter of `range 325`) and
  `catalogue = catalogueFinset W 22 324`, a `Finset` equal to the set `𝓗` of the first
  twenty-two primes above `324` in each unit class modulo `W = 4·324#` (`coe_catalogue`, a proved
  theorem).

### 1.2 Comparison with 22P_AP (nt-22p §3.3)

The note states: *for every `K` the set `G′ = {p ∈ G : p > max S_b}` contains an arithmetic
progression `x, x + v, …, x + Kv` with `x ≥ 1` and `v ≥ 1`*, where `G` is the set of good slope
primes, `S_b = S_ht ∪ 𝓗`.

| Item | Note | Lean | Verdict |
| --- | --- | --- | --- |
| quantifiers | `∀ K ∃ x, v` | `∀ K : ℕ, ∃ x v : ℕ` | CORRECT |
| length | `K + 1` terms `x + jv`, `0 ≤ j ≤ K` | `∀ j ≤ K` | CORRECT |
| `x ≥ 1`, `v ≥ 1` | yes | `1 ≤ x ∧ 1 ≤ v` | CORRECT |
| goodness | `p ∈ G` | `GoodSlopePrime (x + j * v)` | CORRECT (see 1.3) |
| lower bound | `p > max S_b` | `∀ q ∈ S_b, q < p` | CORRECT: equivalent, since `S_b` is a non-empty `Finset` (it contains `2`) |
| `S_b` | `S_ht ∪ 𝓗` | `S_ht ∪ catalogue` | CORRECT: same set, finite, primes only |

Junk values. `K = 0` asks for one good prime above `max S_b` and an arbitrary `v ≥ 1`; this is
implied by the infinitude of `G`, which Proposition D gives. The arithmetic is in `ℕ` with only
additions and multiplications, so there is no truncated subtraction. `S_b` is neither empty nor
too small: it is the full set of the note (a smaller set would make the hypothesis weaker, which
the kernel would have caught only if the proof needed the missing primes), and it is finite, so the
hypothesis is not false for a trivial reason (an infinite `S_b` would make it false and the variant
vacuous). `x ≥ 1` is redundant (`x` is a prime) and harmless. CORRECT.

### 1.3 The definition `GoodSlopePrime` is the set `G` of Proposition D

`GoodSlopePrime` is not new on this branch (it is in `PrimePattern.lean` on `main`, consumed by
field 3 of `GoodSlope`). I checked that it defines the set whose density Proposition D computes:

- by hand: for `p` odd with `2` a square mod `p` and `d(r) = 75 − 53r ≠ 0`, the curve
  `y² = x³ − d(r)²x` has discriminant `64 d(r)⁶ ≠ 0` mod `p`, so it is the good reduction of
  `E : y² = x³ − (75 − 53√2)²x` at the place `√2 ↦ r`, and `pointCount` (affine solutions plus the
  point at infinity) is its order. The two roots `±r` give the two places; the condition is
  symmetric in them. At `p = 2` the root `r = 0` gives two curves with `3` points each, so `2` is
  not good. At `p = 7` both roots kill `d` or `d̄` (`75 − 53·3 = −84`). CORRECT.
- by an independent computation: a literal transcription of the Lean definition (point counts
  over `𝔽_p`, existential over the roots) agrees with the CM description of nt-22p §2.1
  (`p ≡ 1 mod 8`, `(7/p) = −1`, no odd `ℓ | gcd(a, p + 1)` for `p = a² + b²`, `a` odd) at every
  prime `324 < p < 20000` (240 good primes, no mismatch). The relative density of the CM set in
  `(324, 2·10⁶)` is `15821/148867 = 0.1063`, against the Euler product
  `(1/8)∏_{ℓ ≡ 1 (4)}(1 − 2/(ℓ − 1)²) = 0.1060`. The good primes below `324` are
  `17, 41, 73, 97, 241, 257, 313`. As a sanity check against a hidden local obstruction, the good
  primes in `(324, 3·10⁵)` contain a ten-term progression (`53681 + 9240j`, `0 ≤ j ≤ 9`).
  CORRECT.

### 1.4 What Green–Tao 2008 and Proposition D give

**Green–Tao 2008, Theorem 1.2.** I read the statement in the TeX source of arXiv math/0404188v6
(the second theorem of §1, label `sz-primes`, numbered 1.2): *let `A` be any subset of the primes
of positive relative upper density, `limsup_{N→∞} π(N)^{−1}|A ∩ [1, N]| > 0`; then `A` contains
infinitely many arithmetic progressions of length `k` for all `k`.* The progressions are
non-trivial (common difference `d ≠ 0`; with `d = 0` the theorem would be empty). The docstring of
`GoodPrimeAP` quotes this correctly, with the right theorem number. Its proof in the paper is an
outline: §10 says that the method "also extends" to Theorem 1.2, the one change being a
pigeonholed residue class `b mod W`, and leaves the details to the reader. The Conlon–Fox–Zhao
exposition (arXiv:1403.2957) proves Theorem 1.1 in full and lists the dense-subset form only as
an extension. The docstring records this caveat (from `rv-nt22p-ap`, F3). CORRECT as a citation;
the caveat stands (finding F3 below).

**Proposition D** (nt-22p §2.2): `G` has natural density `(1/8)∏_{ℓ ≡ 1 (4)}(1 − 2/(ℓ − 1)²)`
in the primes. Only its weakest consequence is used: `G` has positive relative upper density.
It is a proof sketch (Hecke's theorem for `ℚ(i)` or the prime number theorem in progressions, plus
the two-dimensional sieve of the manuscript, lines 1600–1642); `rv-nt22p-ap` finds it correct as a
sketch and lists what the write-up must contain (its F5). UNCHECKED here beyond the numerical
agreement of 1.3; it is the one unwritten step between the published theorem and `GoodPrimeAP`
(finding F2 below).

**The derivation.** Write, in Lean,

```lean
def GreenTaoDense : Prop :=
  ∀ A : Set ℕ, (∀ p ∈ A, p.Prime) →
    (∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N in atTop,
      δ * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)) →
    ∀ k : ℕ, ∃ x d : ℤ, d ≠ 0 ∧ ∀ j : ℕ, j < k → ∃ p ∈ A, (p : ℤ) = x + j * d

def PropDUpper : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N in atTop,
    δ * (Nat.primeCounting N : ℝ) ≤
      (((Finset.range (N + 1)).filter ZInQ.GoodSlopePrime).card : ℝ)

theorem goodPrimeAP_of_greenTao_propD (hGT : GreenTaoDense) (hD : PropDUpper) :
    ZInQ.GoodPrimeAP
```

`GreenTaoDense` is Theorem 1.2 with "infinitely many progressions" weakened to "one", and with
`limsup > 0` written as "`δπ(N) ≤ |A ∩ [0, N]|` for infinitely many `N`, for some `δ > 0`". The two
forms are equivalent: the ratio lies in `[0, 1]` because `A` consists of primes, so a positive
limsup `λ` gives the second form with `δ = λ/2`, and the second form gives `limsup ≥ δ`; and
`0 ∉ A`. `PropDUpper` is implied by the natural-density statement of Proposition D. The
derivation: put `M = max S_b` and `A = {p ∈ G : p > M}`. Then
`|A ∩ [0, N]| ≥ |G ∩ [0, N]| − (M + 1)`, and `π(N) → ∞` (`Nat.tendsto_primeCounting`), so `A`
satisfies the density hypothesis with `δ/2`. Theorem 1.2 with `k = K + 1` gives `x, d ∈ ℤ`,
`d ≠ 0`, and primes `p_j = x + jd ∈ A` for `j ≤ K`. If `d > 0`, take `x′ = p₀` and `v = d`; if
`d < 0`, reverse: `x′ = p_K`, `v = −d`, and `x′ + jv = p_{K−j}`. Then `x′ ≥ 2`, `v ≥ 1`, and every
term is in `G` and exceeds every element of `S_b`. No condition beyond the two inputs is used.

I compiled this derivation against the branch (`scratch` file, not part of the repository); see
§4 for the outcome. <!-- DERIVE -->
