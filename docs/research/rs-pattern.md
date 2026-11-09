# The fixed prime pattern (22P) and its interaction with the catalogue (CAT)

Status: research note, 2026-11-08. Each claim carries a mark:
**VERIFIED** (checked against the manuscript, the Lean source or a computation, which is cited),
**STANDARD** (a published theorem, with reference) or **SPECULATIVE** (an unproved idea).
Manuscript line numbers refer to `diophantine_zq.tex` (11/5 version); audit records are those of
`docs/theorem-application-audit/applications.json`.

Notation. `𝒞 = {0, −15, −20, −24, −30, −60}`, `F(t) = ∏_{c∈𝒞}(t − c)`, `K₀ = ℚ(s)`, `s² = 2`,
`E : y² = x³ − d²x` with `d = 75 − 53s` (so `N(d) = 7`), `P_s = ∏_{q≤324} q`, `W = 4P_s`,
`𝓗` the catalogue (the first 22 primes above 324 in each unit class mod `W`),
`S_ht = {q ≤ 324}`, `S_b = S_ht ∪ 𝓗`, `B_q = 4` on `S_ht` and `B_q = 1` on `𝓗`, `c_* = 4M₀`.
For a prime `p` that splits in `K₀`, with `r² ≡ 2`, let `d₁, d₂` be the orders of the groups of
`y² = x³ − (75 ∓ 53r)²x` over `𝔽_p`. A slope `t ∈ ℚ` has an *odd contact prime* `p` if
`v_p(t − c)` is positive and odd for some `c ∈ 𝒞`.

**Summary.**

- 22P is used at exactly one point: to produce, for each integer `A`, three slopes summing to `A` that satisfy the four conditions `GoodSlope`.
- The proof needs much less than 22P states:
  - 18 of the 22 forms, not 22;
  - square factors are allowed;
  - no catalogue multipliers and no bound `B₀`;
  - `p ∤ d₁d₂` is never used;
  - one of the three slopes can be a fixed constant.
- With these reductions the needed configuration becomes a translation-invariant prime pattern: a homothetic copy of a 12-point set inside the good primes.
- Two things cannot be weakened inside the present architecture:
  - each slope needs about six prime values of linear forms at once, with every odd-exponent prime individually "good";
  - goodness includes a condition on the Frobenius element that is not a congruence condition.
- No route reduces 22P to Dirichlet's or Chebotarev's theorem without replacing the six-contact height theorem and the one-group-per-prime test.
- The catalogue `𝓗`, and with it CAT, exists only to serve the manuscript's proof of 22P. It can be removed from the construction. That would eliminate CAT without the effective Dirichlet theorem.

---

## 1. The statement and every use

### 1.1 The statement

Manuscript, Proposition 6.2 (`prop:fixed-prime-pattern`, lines 1267–1289; proof lines 1291–1704).
For every `A ∈ ℤ` and every real `B₀` there are `u₁, u₂, v ∈ ℤ`, `v ≠ 0`, such that with
`u₃ = Av − u₁ − u₂` each of the twenty-two values

    v,   u_j − b v   (1 ≤ j ≤ 3, b ∈ 𝓑 = 𝒞 ∪ {1})

equals `ε k p` with `ε = ±1`, `k ∈ 𝓚 = {d h : d | P_s⁴, h ∈ 𝓗}` and `p > B₀` a prime that splits in
`ℚ(√2)`, has good reduction at both places, and satisfies `gcd(d₁, d₂) = 4`, `p ∤ d₁d₂`.

Lean: `ZInQ.FixedPrimePattern` (`ZInQKernel/Hypotheses/PrimePattern.lean`), with
`ZInQ.GoodPatternPrime`, `ZInQ.patternValues`, `ZInQ.catalogueMultipliers`. The Lean statement
matches the manuscript's (VERIFIED by reading both).

### 1.2 Uses in Lean

`FixedPrimePattern` appears as a hypothesis along the following chain. It is destructured at one
place only, `ZInQ.Mult.pattern_slopes` (VERIFIED: `grep FixedPrimePattern ZInQKernel`):

| Declaration | File | Role |
| --- | --- | --- |
| `ZInQ.Mult.pattern_slopes` | `Multiplication/Completeness/PatternSlopes.lean:262` | **the only consumer**: `∀ A B₀, ∃ t : Fin 3 → ℚ, ∑ t = A ∧ ∀ j, GoodSlope B₀ (t j)` |
| `ZInQ.Mult.slopes_of_int` | `Multiplication/Completeness/Core.lean:16` | calls `pattern_slopes h22 A 0`, i.e. **with `B₀ = 0`**, then `slope_complete` |
| `ZInQ.Mult.completeness_core` | `Core.lean:36` | the nine integers `a_{ij}, b_i` of a true triple, each a sum of three slopes |
| `ZInQ.Mult.multiply_complete` | `Multiplication/Completeness/Template.lean:24` | completeness of the multiplication template |
| `multiplication_exact`, `multiplication_existsUnique` | `Multiplication/Top/Exact.lean` | soundness plus completeness |
| `ZInQ.Assembly.main_branch_eq`, `value_relation_iff`, `exists_value_relation_iff` | `Assembly/Top/ValueRelation.lean` | the value relation |
| `Pstar_spec`, `assembly`, the three `exists_bounded_integer_polynomial_defining_integers_*` | `Assembly/Top/Assembly.lean`, `Main.lean` | the main theorem |

`GoodSlope B₀ t` (`PatternSlopes.lean`) has four fields:

1. `t ∉ 𝒞`, `t ≠ 1`;
2. `old`: for `q ∈ S_b`, `|v_q(t − 1)| ≤ B_q` and `|v_q(F(t)/(t − 1)⁸)| ≤ 8B_q`;
3. `contact`: every odd contact prime `p ∉ S_b` satisfies `B₀ < p`, `GoodPatternPrime p`, and every positive contact valuation at `p` equals 1;
4. `few`: there are at most six such primes.

Which parts are actually consumed (VERIFIED, by reading the consumers):

- `slope_complete` (`SlopeCompleteness.lean`) and `pole_input_valuations` / `padicValRat_contactQuot_eq_one` (`PoleValuations*.lean`) use fields 1, 2, 4, and from field 3 the goodness and the valuation-one statement. **The `B₀ < p` component is discarded at both places** (`obtain ⟨-, hgood, -⟩`, `SlopeCompleteness.lean:123`; `obtain ⟨-, -, hone⟩`, `PoleValuationsAux.lean:140`).
- `exists_shift` (`SlopeCompleteness.lean:47`) uses from `GoodPatternPrime p` only:
  - the root `r` of `X² − 2`;
  - `75 ∓ 53r ≠ 0`;
  - `gcd(d₁, d₂) = 4`.

  It **discards** `p ≠ 2` and `p ∤ d₁d₂`. It feeds these to `shift_choice'` (`ShiftChoice.lean`), which needs only `gcd(d₁, d₂) = 4`, and to `tests_precision_selected` (`SelectedPrecision.lean:80`), which needs `324 < p`, `r`, `75 ∓ 53r ≠ 0`, `d₁ | h` and `d₂ | h − c_*`.
- `pattern_slopes` uses the pattern values as follows:
  - `v` and `u_j − v` enter only field 2. At primes outside `S_b`, the value `v` is used once, to know `v_q(v) ∈ {0, 1}` (`hv01`), which is automatic for a slope written in lowest terms.
  - The eighteen contact values `u_j − cv` enter fields 1–4.
  - `B₀` is raised to `max(B₀, 324, max 𝓗)` only to keep the pattern primes outside `S_b`.

### 1.3 Uses in the manuscript

Proposition 6.2 is applied once, at lines 1705–1758 ("Apply this construction to the nine integral
homogeneous quantities"), to prove completeness of the multiplication template **M**. **M**'s
completeness is needed for the natural predicate (line 369, Lagrange) and for the precision
computation. It is never used in soundness (line 1258: "the sound direction … does not use pole
completeness"; soundness needs neither PC nor 22P). VERIFIED.

### 1.4 What completeness does with each value

For a true triple `(n₁, n₂, n₁n₂)`, each of the nine integers is written as `t₁ + t₂ + t₃`, and
each slope `t` must pass the slope predicate (lines 1177–1235). At each odd contact prime `p ∉ S_b`
of `t`, one of the six test groups must succeed at `p`. VERIFIED, lines 1705–1758 and
`slope_complete`.

- **One group per prime.** The trace `Θ = Tr Σ_g W_g^{-1}` has `12` summands, each `≡ 0` or `1 mod p`. The pole input `B = R/Θ²` has `v_p(B) = v_p(R) − 2v_p(Θ)`, and Lemma `lem:pole` (line 988) forbids a negative odd valuation. So some group must have all twelve normalized tests integral at a place above `p`. There are six groups, hence at most six odd contact primes per slope (field 4). With six contact values per slope, this is why 22P gives each value exactly one large prime.
- **Splitting in `ℚ(√2)`.** The first eight tests place `H = [h]P₀` in the formal group at `𝔭 = (p, s − r)`, and `V₀ = H − [c_*]P₀` in the formal group at the conjugate place. With `p` inert the two places coincide, which would force `[c_*]P₀ ≡ O`. That happens for only finitely many `p`.
- **The gcd condition.** One needs `h ≡ 0 (mod lcm(M₀, d₁))` and `h ≡ c_* (mod d₂)` (line 1710). This is solvable when `gcd(d₁, d₂) = 4`. More generally it is solvable exactly when `gcd(lcm(M₀, e₁), e₂) | c_*` for the orders `e_i` of `P₀` at the two places, i.e. when `gcd(e₁, e₂) | 4M₀`. (VERIFIED: `gcd(lcm(M₀,e₁), e₂) = lcm(gcd(M₀,e₂), gcd(e₁,e₂))`.)
- **Contact valuation one.** At an odd contact prime with `v_p(t − c) = e` and `v_p(t − 1) = 0`, one has `v_p(RC²) = 2v_p(D) − (2k − 1)e`. A group therefore contributes residue 1 only if `v_p(D) ≥ ke − (e − 1)/2`.
  - For `k = 25` this means `v_p(D) ≥ 25` when `e = 1`, and `v_p(D) ≥ 74` when `e = 3`.
  - The truncated logarithm gives accuracy 28 (`tests_precision_selected`; line 1161).
  - So `e = 1` is required.
- **Old primes.** The bounded valuations at `S_b` (field 2) let the fixed constant `ℓ₀ = 12P_s^{2916}H_cat^{732}` clear the pole input there (lines 1724–1745).
- **Catalogue multipliers.** In 22P each value is `ε d h p`. The catalogue prime `h` is an old prime, cleared by `ℓ₀`, so it is not an odd contact prime; this is the only reason `𝓗 ⊂ S_b`.

---

## 2. The weakest form the proof needs

### 2.1 The exact interface

The Lean proof would go through unchanged with 22P replaced by the following statement
(VERIFIED: it is literally what `slopes_of_int` consumes).

> **(SR) Slope representation.** For every `A ∈ ℤ` there are `t₁, t₂, t₃ ∈ ℚ` with
> `t₁ + t₂ + t₃ = A` and `GoodSlope 0 tⱼ` for each `j`.

Spelled out, with the unused parts of `GoodPatternPrime` removed, each `t = tⱼ` must satisfy:

- (a) `t ∉ 𝒞 ∪ {1}`;
- (b) `|v_q(t − 1)| ≤ B_q` and `|v_q(F(t)/(t − 1)⁸)| ≤ 8B_q` for `q ∈ S_b`;
- (c) every prime `p ∉ S_b` with `v_p(F(t))` odd and positive has `v_p(F(t)) = 1`, `p` splits in `ℚ(√2)`, both reductions are good, and `gcd(d₁, d₂) = 4`;
- (d) there are at most six such `p`.

For `p > 324` at most one contact `c` has `v_p(t − c) > 0`, so "odd contact prime outside `S_b`"
means the same as "prime outside `S_b` dividing `F(t)` to an odd power". In other words, `t` is the
abscissa of a point on the quadratic twist `D y² = F(x)` of the genus-2 curve `y² = F(x)`, where
`D` is, up to `S_b`, a product of at most six good primes (VERIFIED, elementary).

### 2.2 Relaxations relative to 22P

| Relaxation | Mark | Source |
| --- | --- | --- |
| `B₀` plays no role: only `p ∉ S_b` is needed | VERIFIED | `Core.lean:22`; the discarded components in §1.2 |
| `p ∤ d₁d₂` and `p ≠ 2` are never used | VERIFIED | `exists_shift` |
| `gcd(d₁, d₂) = 4` may be weakened to `gcd(d₁, d₂) | c_*`, or to `gcd(e₁, e₂) | c_*` for the orders of `P₀` | VERIFIED (elementary; needs a one-lemma change to `shift_choice`) | §1.4 |
| Only the 18 contact values `u_j − cv` (`c ∈ 𝒞`) need conditions at large primes; `v` and `u_j − v` need only the congruence conditions (b) at `S_b` | VERIFIED | `goodSlope_of_values`, field 2 |
| Square factors are allowed: a value may be `(S_b-part)·m²·p` or `(S_b-part)·m²` | VERIFIED | (c) concerns odd exponents only |
| A slope's six primes may be spread arbitrarily over its six contact values | VERIFIED | field 4 counts primes per slope |
| No common denominator is needed | VERIFIED | (SR) |
| No catalogue multiplier is needed: multipliers `d | P_s⁴` suffice, and in fact `d ∈ {1, 2, 8P_s}` | VERIFIED (computation, §2.4) | `pattern_value_spec` |
| One of the three slopes may be a fixed constant, e.g. `t₃ = −10` | VERIFIED (computation, §2.5) | `GoodSlope 0 (−10)` holds with `P = ∅` |

The good-prime density changes little under the gcd relaxation (VERIFIED, computation
`scratch/rs-pattern/good_primes.py`).

- Range: all 17,980 primes `7 < p ≤ 2·10⁵`.
- The point-count definition `GoodPatternPrime` agrees with the CM description of §3.2 (no exception).
- 1,925 primes are good, i.e. 10.7% of all primes.
- Primes with `p ≡ 1 (mod 8)` and `(p/7) = −1`: 12.6% of all primes. Of these:
  - 84.8% satisfy `gcd(d₁, d₂) = 4`;
  - 87.7% satisfy `gcd(e₁, e₂) | 4`.

### 2.3 What cannot be weakened (inside the present construction)

- **At most six odd contact primes per slope.** Each test group costs 162 witnesses (`test_group`, line 6747). The polynomial's variable count is fixed: `FrozenTarget` has exactly `292,890,231,904` witness variables, equal to the construction's count (`ZInQ.Syntax.witness_count_arith`). The multiplication template (35,134 witnesses) is instantiated `98,382 + 15,845·190 = 3,108,932` times. So one extra witness in it costs more than three million variables. A seventh group per slope does not fit (VERIFIED). Fewer witnesses are always allowed.
  Strictly, one group could serve several primes `p, p′` if their conditions on its shift `h` are compatible. That requires cross-conditions such as `gcd(e₁(p), e₂(p′)) | c_*` between the reduction orders at different primes, which are even less controllable than the gcd condition. So the cap is effectively six primes per slope.
- **Each odd-exponent prime outside `S_b` must be good individually, with exponent exactly 1** (§1.4).
- **Bounded valuations at `S_b`** (field 2). An unbounded `v_q(t)` at an old prime makes `v_q(RC²)` for `k = 25` tend to `−∞`. The fixed `ℓ₀` and `c_*` cannot compensate: the conjugate-place tests have bounded `q`-adic depth because `h − c_*` does.
- **Every `A`.** The nine integers are coordinates of `[n]P₀` with a free common positive scale. The scale does not reduce the problem to a special set of `A` in any evident way.

### 2.4 A catalogue-free form of 22P

> **22P′.** As 22P, with `𝓚` replaced by `{d : d | P_s⁴}`.

22P′ implies (SR) by the existing `pattern_slopes` argument. In `pattern_value_spec` the
catalogue clause becomes `v_h(d) = 0` (VERIFIED, by inspection of the proof).

22P′ is as provable as 22P. The manuscript's proof uses the catalogue only in "The fixed
multipliers and initial progression" (lines 1320–1380), to put each cofactor `p` in the residue
classes `1 mod 8`, `3 mod 7` and `1 mod q`. The following explicit choice does this with no
catalogue prime:

- `u₁ ≡ u₂ ≡ ρ (mod W₀)` and `v ≡ 8P_s ω (mod W₀)`;
- `W₀ = 2⁹P_s²`;
- `ρ, ω ≡ 1 mod 16`, `≡ 3 mod 7`, `≡ 1 mod q` for the other odd `q ≤ 324`;
- the box is `u₁, u₂ ∈ (X, 2X)`, `0 < v < X/(2(|A| + 62))`.

Every value is then `≡ u_j (mod q)` for each odd `q ≤ 324`. The multipliers are as follows:

- the values with `j = 1, 2` are units with multiplier 1;
- `u₃ = Av − u₁ − u₂ ≡ −2ρ` has 2-adic valuation exactly 1, and `−(u₃ − bv)/2 ≡ ρ`, so the multiplier is 2 with sign −1;
- `v` has multiplier `8P_s`, with `v₂(8P_s) = 4 ≤ B₂`.

Sum parity forces `u₃` to be even, which is why multiplier 2 cannot be avoided in the
three-slope form. VERIFIED (computation `scratch/rs-pattern/local_choice.py`), for 30 values of
`A` (including `0, ±1, ±60, 10⁶, 3⁴⁰` and random 100-bit values). For all 22 forms:

- `k_ν | P_s⁴`;
- `W₀` times every coefficient is divisible by `k_ν · 8∏_{odd q≤324} q`, so `k_ν` and the classes are constant on the whole progression;
- the cofactor is `≡ 1 mod 8`, a non-residue mod 7, and `≢ 0, −1 mod q`;
- the same holds at 30 random points of the box.

The rest of the manuscript's proof applies unchanged with `Q_* = 324`. SPECULATIVE only in that
the adaptation has not been written out line by line. It touches no estimate.

### 2.5 The two-slope form: a translation-invariant pattern

`t₃ = −10` satisfies `GoodSlope 0`, with no odd contact prime outside `S_ht` (VERIFIED, computation
`scratch/rs-pattern/free_slopes.py`):

- its contact values are `−10, 5, 10, 14, 20, 50`, and `t₃ − 1 = −11`;
- the largest valuation of `F(t)/(t − 1)⁸` is `|v₁₁| = 8 ≤ 32`.

Then `t₁ + t₂ = A + 10 =: A′`. With `t₁ = u/v`, the contact values of `t₂ = A′ − t₁` are
`−(u − (A′ − c)v)/v`, so all twelve numerators are values `u − c′v`, `c′ ∈ S_A := 𝒞 ∪ (A′ − 𝒞)`:

> **22P₂.** For every `A ∈ ℤ` there are `u, w ∈ ℤ` with `w` odd and `v_q(w) ≤ 3` for odd `q ≤ 324`,
> such that, with `v = 8P_s w`, every number `u − c′v` (`c′ ∈ 𝒞 ∪ (A + 10 − 𝒞)`) is a good prime
> greater than `max 𝓗`. In the current construction, also require that no square of a catalogue prime
> divides `w`, `u − v` or `u − (A + 9)v`.

22P₂ implies (SR) with `t = (u/v, A + 10 − u/v, −10)` (VERIFIED by hand):

- at `q ≤ 324`: `|v_q(t − 1)| = v_q(v) ≤ 4` and `v_q(F(t)/(t − 1)⁸) = 2v_q(v)`;
- at `h ∈ 𝓗`: the square-freeness clause bounds both quantities by `1` and `8`;
- each of `t₁, t₂` has exactly its six pattern primes as odd contact primes.

No multiplier is needed at all, and the multiplication template is unchanged.

Examples (VERIFIED, computation `scratch/rs-pattern/psearch.c` with the independent checker
`verify_hits.py`). The search uses a scaled-down model in which the old primes are `{2, 3, 5, 7}`
in place of `S_ht`:

- `u ≡ 241 (mod 1680)` and `v = 1680w`, so that every value is `≡ 1 (mod 8)` and `≡ 3 (mod 7)`;
- for each of `A ∈ {0, ±1, ±2, 5, 13, 61, ±100, ±1000, 12345, 99991}`, configurations were found for the three-slope form, the difference form `t₁ − t₂ = A` (§4, R3) and the two-slope form 22P₂ (each prime below `4·10¹¹`);
- every slope was checked against the analogue of `GoodSlope`.

These are sanity checks of the local recipes, not evidence for the theorem.

### 2.6 Quantitative slack, in one table

| Quantity | 22P provides | The proof needs |
| --- | --- | --- |
| size of the prime | `> B₀`, every `B₀` | `> max 𝓗` (or `> 324` with the catalogue removed) |
| forms with a prime condition | 22, in 3 variables | 18 (three slopes), or 12 in 2 variables (22P₂) |
| multipliers | `d h`, `d | P_s⁴`, `h ∈ 𝓗` | `d | P_s⁴`; `d ∈ {1, 2, 8P_s}` suffice; none for 22P₂ |
| shape of each value | `±k·p` | `±(S_b-part)·m²·p` or `±(S_b-part)·m²`, ≤ 6 primes per slope |
| goodness | split, good reduction, `gcd(d₁, d₂) = 4`, `p ∤ d₁d₂` | split, good reduction, `gcd(d₁, d₂) | c_*` |
| number of good primes per slope | exactly 6 | ≤ 6 (no slack upward: witness budget) |

---

## 3. The manuscript's proof of 22P and its trust leaves

### 3.1 Structure (lines 1291–1704)

1. **Box and signs** (1314–1318). An open box `Ω ⊂ ℝ³` avoiding the 22 zero planes; signs `ε_ν`. Elementary.
2. **Fixed multipliers and initial progression** (1320–1380). A residue mod `q⁸` for each `q ≤ 324`; catalogue primes `h_ν` adjust the unit classes; CRT gives `r₀ mod W₀`. Uses the existence of the catalogue (Dirichlet, **A057**). The catalogue's size bound (CAT, **A046**) is a separate matter, needed only by the size chapter.
3. **Lower count** (1382–1453). A sieve density `≥ c_A (log L)^{−44}` from Mertens in progressions (Williams, **C035**). Then, for each residue `r` modulo `W_L`, the Green–Tao asymptotic for the 22 affine forms `ε_ν F_ν(r + W_L n)/k_ν` (**C036–C039**, record **A021**). The singular product is bounded below uniformly in `L`, and proper prime powers are removed.
4. **Upper sieve with uniform constants** (1455–1552). A self-contained Selberg sieve in two variables, with Mertens in the progression `1 mod 4` (**C040**, **C041**). Elementary given Mertens.
5. **Conjugate orders** (1554–1598). For `p ≡ 1 (mod 8)` with `(7/p) = −1`, the CM computation (**C042–C045**, record **A072**). The two reductions are opposite twists of `y² = x³ − x`, with `d₁, d₂ = p + 1 ∓ 2a` where `p = a² + b²` (`a` odd). The 2-part of `gcd(d₁, d₂)` is 4, and an odd prime `ℓ` divides `gcd(d₁, d₂)` iff `ℓ | a` and `ℓ | p + 1` (i.e. `b² ≡ −1 mod ℓ`). The progression excludes `ℓ ≤ L` (via `Ψ_ν ≢ −1 mod q`).
6. **Bad prime values** (1600–1642). An upper-sieve count of `p = a² + b²` with `ℓ | a`, `b² ≡ −1 (mod ℓ)`, `ℓ > L`: `≪ X/(L log X) + X^{7/8} + √X log X`. Elementary given step 4.
7. **Patterns on a fiber** (1644–1680). An upper sieve on each fiber `F_ν = c`: `≪ X²/(log X)²¹`.
8. **Order of choices** (1682–1704). `L` first, so that the `1/L` tail is below half the main term; then `X`.

### 3.2 Trust leaves

| Leaf | Precise statement used | Where | Audit |
| --- | --- | --- | --- |
| Green–Tao, *Linear equations in primes*, Ann. of Math. 171 (2010), Main Theorem p. 1763 | For a system `Ψ : ℤ^d → ℤ^t` of affine forms of finite complexity `s` and a convex body `K ⊂ [−N, N]^d`, `Σ_{n∈K} ∏ Λ′(ψ_i(n)) = β_∞ ∏_p β_p + o(N^d)`, conditionally on GI(`s`) and MN(`s`) | step 3, with `s ≤ 20` (Def. 1.5, singleton classes) | A021 (C036, C039) |
| Green–Tao, *The Möbius function is strongly orthogonal to nilsequences*, Ann. of Math. 175 (2012), Thm 1.1 | MN(`s`) for every `s` | step 3 | A021 (C037) |
| Green–Tao–Ziegler, *An inverse theorem for the Gowers `U^{s+1}[N]`-norm*, Ann. of Math. 176 (2012), Thm 1.3 (arXiv v5 with the separate erratum: Prop. 3.1 and the modified deduction of Prop. 7.3) | GI(`s`) for every `s` | step 3 | A021 (C038) |
| K. S. Williams, *Mertens' theorem for arithmetic progressions*, J. Number Theory 6 (1974), Thm 1 | `Σ_{p≤x, p≡a (q)} 1/p = (log log x)/φ(q) + C_{q,a} + O(1/log x)` | steps 3, 4 | A021 dependency (C035, C040, C041) |
| Silverman, *AEC*, III.7.4, V.2.3.1(b), III.8.6, V.1.1 | `End ⊗ ℚ_ℓ ↪ End(V_ℓ)`; Frobenius integral; trace and degree; Hasse bound | step 5 | A072 (C042–C045) |
| Dirichlet's theorem (Mathlib: `Nat.forall_exists_prime_gt_and_modEq`) | every unit class contains primes | catalogue (step 2) | A057 |

Only the first three rows are deep. All three are STANDARD. The Mertens and Silverman inputs are
textbook, and their CM part is needed only to identify the good primes. In Lean, goodness is
stated through point counts (`GoodPatternPrime`), so any proof of 22P has to establish the CM
description as well.

---

## 4. Candidate cheaper routes

The routes fall into three groups:

- **R1–R3** simplify the hypothesis and remove CAT; they do not change the depth of 22P;
- **R4** is the only candidate that lowers the depth of the trust leaf;
- **R5–R8** are attempts at a Dirichlet- or Chebotarev-level proof. Each fails for a reason identified below.

### R1. State the hypothesis as (SR), or as 22P′ / 22P₂

- *Idea.* Replace `FixedPrimePattern` by the weakest statement the proof consumes (§2.1), or by one of the prime-pattern forms 22P′ (§2.4) and 22P₂ (§2.5).
- *Replaces.* The hypothesis statement only. `pattern_slopes` becomes trivial for (SR), and stays a short adaptation for 22P′ and 22P₂.
- *Why it works.* VERIFIED in §1.2 and §2.1–2.5.
- *Obstacle.* None mathematically. (SR) is less transparent than a prime-pattern statement, so 22P₂ is the better public form.
- *First test.* Prove `pattern_slopes` from 22P₂ in Lean; this is a variant of `goodSlope_of_values` with the constant slope `−10`.
- *Success criterion.* The main theorem builds with `h22 : TwoSlopePattern`.

### R2. Remove the catalogue from the construction (eliminates CAT)

- *Idea.* The catalogue `𝓗` enters the polynomial only through `N_s = P_s H_cat` (hence `M₀`, `c_*`), `ℓ₀ = 12 P_s^{2916} H_cat^{732}`, `R = max(D, H_max, c_*, 10¹²)` and `S_mul` (lines 238–241, 6273–6282; Lean `Syntax/Constants/Fixed.lean`, `Multiplication/Certificate/Constants.lean`). Its only mathematical role is to supply the multipliers `h_ν` in the proof of 22P (§1.4; VERIFIED: no other consumer of `catalogue` outside the size chain and the multiplication constants, by `grep`). With 22P′ or 22P₂, set `N_s = P_s`, `ℓ₀ = 12P_s^{2916}`, `S_b = S_ht`, `S_mul = S_ht ∪ supp(c_*)`.
- *Replaces.* CAT entirely, and with it the effective Dirichlet theorem planned in `docs/effective-dirichlet-plan.md`. The witness count does not change, since the constants are scalars.
- *Why it might work.* Every bound in the size chain gets smaller: `M₀ ≤ P_s^{10}` by the same argument as lines 6320–6347, and `R = D` still. Completeness needs only (SR) relative to the new `S_b`, which 22P′ and 22P₂ supply with no catalogue. Soundness is unaffected: from `p ∉ S_mul` it uses only `324 < p`, `p ∤ c_*` and `v_p(ℓ₀) = 0`, together with the admissibility of `S_mul` for the height estimate (`not_mem_S_mul`, `S_mul_admissible` in `Soundness/LocalCongruence.lean` and `Soundness/ContactSupport.lean`). All of these persist when `𝓗` is removed (VERIFIED, by reading).
- *Obstacles and what it breaks.*
  - It changes the polynomial `P_*`. It no longer coincides with the upstream saved construction (`construction/ordinary-integer-definition.json`), which is a cross-check, not a proof input (KERNEL_PLAN.md).
  - It departs from the manuscript's literal `P_*`.
  - It touches `Syntax/Constants/{Fixed,Catalogue,Relations}`, `Size/Constants/*`, `Size/Majorants/Cutoff`, `Multiplication/Certificate/{Constants,ConstantsProperties}`, `Completeness/{PatternValues,SbIntegrality,PatternSlopes}` and the hypothesis file.
- *First test.* Rewire `Syntax.Ns` to `Ps` in a branch and see which size lemmas break; most should simplify.
- *Success criterion.* The main theorem takes H, PC and 22P′ (or 22P₂) only; no `CatalogueBound`.

### R3. Translation-invariant patterns: two slopes or a difference

- *Idea.* The sum of three slopes has a parity obstruction to translation invariance. If `u_l = σ_l u₁ + κ_l v` for all three slopes, the coefficient of `u₁` in `Σ u_l = Av` is `1 + σ₂ + σ₃ ≠ 0`. For two slopes, `t₁ ± t₂ = A′`, all numerators are values of `u − c′v` for `c′` in a fixed 12-point set, i.e. a homothetic copy of a finite set. This is reachable either without changing the template, by fixing `t₃ = −10` (22P₂, §2.5), or with a smaller template, by using two slopes per quantity. The latter saves `9·1,298` witnesses per multiplication, which is allowed.
- *Replaces.* The system in 3 variables (18 contact forms of true complexity at least 4, or at least 5 with the shift `b = 1`; not translation-invariant) by a 12-point pattern on a line (true complexity 10, translation-invariant).
- *Why it might work.*
  - Under GTZ the manuscript's proof adapts with fewer forms and 2 variables (fibers become lines; the fiber sieve has dimension 11). SPECULATIVE (routine).
  - It needs no multipliers and no catalogue (§2.5, VERIFIED).
- *Obstacle.* For GTZ the complexity rises from about 4 to 10. This does not matter for trust: Theorem 1.3 of GTZ covers every `s`. The gain is structural; it is what makes R4 conceivable.
- *First test and criterion.* As R1.

### R4. Green–Tao 2008 instead of Green–Tao–Ziegler, for 22P₂

- *Idea.* By Green–Tao (*The primes contain arbitrarily long arithmetic progressions*, Ann. of Math. 167 (2008), Thm 1.2; STANDARD), every subset of the primes of positive relative upper density contains `k`-term progressions for every `k`. Hence it contains a homothetic copy of `−S_A`, which lies in a progression of length `max S_A − min S_A + 1`.
  - The good primes have positive relative lower density. Start from the Chebotarev class `p ≡ 1 (8)`, `(p/7) = −1` (density `1/8`). Keeping only the primes in it with `p ≢ −1 (mod ℓ)` for every odd `ℓ ≤ L` leaves relative density `≍ 1/log L` (STANDARD: the prime number theorem in progressions). The manuscript's bad-prime sieve (step 6) shows that the primes still bad, those with some `ℓ > L`, have relative density `O(1/L)`. For large `L` the difference is positive (SPECULATIVE only in that this is the manuscript's argument transposed, not written out).
  - Numerically about 85% of that class survives (§2.2).
- *Replaces.* GI(`s`) and MN(`s`) (the inverse theorem for all Gowers norms and the Möbius–nilsequence estimate) by Szemerédi's theorem plus the transference principle with the Goldston–Yıldırım majorant.
- *Main obstacle.* 22P₂ also requires the common difference `v` to have bounded valuations at the old primes, `v_q(v) ≤ 4` for `q ≤ 324` (field 2; unavoidable, §2.3). Green–Tao's theorem gives no control of the common difference.
  - Restricting it to a non-intersective set such as `8P_s·(ℤ coprime to P_s)` is false for general dense sets.
  - After the `W`-trick it becomes a pattern with a *different* dense set at each point, which the relative Szemerédi theorem does not handle. As far as I can see this needs Gowers uniformity of the primes in progressions, i.e. GTZ again.
  - SPECULATIVE: a Szemerédi-type theorem in the primes with common difference in a prescribed residue class, provable without the full inverse theorem, may exist in the literature (polynomial or shifted-prime-difference patterns are related: Tao–Ziegler, Wooley–Ziegler). I have not found one. A title-level search turned up "Linear constellations in primes with arithmetic restrictions" (arXiv:2408.17441), which may treat restricted configurations. I have not read it, and it presumably builds on the Green–Tao–Ziegler machinery.
- *First test.* A literature search for "arithmetic progressions in the primes with common difference in a given residue class" (or with difference `8P_s` times a number prime to `P_s`) proved by transference alone.
- *Success criterion.* A citable theorem implying 22P₂ whose proof does not use the inverse theorem for the Gowers norms. A useful partial result: a version with arbitrary `v`, plus a way to remove the side condition by changing the construction. I found no such change (§2.3).

### R5. Sieve methods (fundamental lemma, Selberg, Chen, Bombieri–Vinogradov)

- *Idea.* Accept almost-primes: values whose odd part outside `S_b` has few prime factors.
- *Why it fails.*
  1. Every odd-exponent prime factor must be good individually. Goodness is a Frobenius-class condition (`Frob_p = σ` in `Gal(ℚ(ζ₈, √7)/ℚ)`, where `σ` fixes `ζ₈` and moves `√7`) plus the gcd condition. A congruence on a product controls only the product's class, not each factor's. VERIFIED: goodness forces `(7/p) = −1`, and a product of two good primes has `(7/·) = +1`.
  2. The total number of such primes per slope is at most six, and the witness budget forbids more groups (§2.3). Six contact values with at most six primes leave almost-primes no room.
  3. A sieve of dimension 18 at level `X^{1−ε}` reaches only `z = X^{1/C}`, so large prime factors remain uncontrolled. A "sieve up to `X`" in the style of Iwaniec's half-dimensional sieve exists only for multiplicatively closed conditions (norms), and those cannot express `(7/p) = −1` (R6).
- *Verdict.* Not viable, for structural reasons (VERIFIED as stated).

### R6. Algebraic parametrizations and norm forms

- *Idea.* Choose `(u, v)` on a variety on which some contact values are automatically squares, or norms whose prime factors lie in prescribed classes.
- *Genus obstruction.* (STANDARD, Riemann–Hurwitz; computation as follows.) Requiring `m` of the six values `u − c_i v` to be fixed constants times squares defines a `(ℤ/2)^{m−1}` cover of `ℙ¹` branched at the `m` contacts. Its genus is `g = 1 + 2^{m−3}(m − 4)` for `m ≥ 2`:
  - `g = 0` for `m = 2, 3`;
  - `g = 1` for `m = 4`;
  - `g = 5` for `m = 5`;
  - `g = 17` for `m = 6`.

  So positive-dimensional families have at most 3 square values (rational), or 4 (elliptic). The remaining values become binary forms of degree 2 or 4 in the parameters. Simultaneous prime values of three or more such forms is an open problem (Schinzel's Hypothesis H type), harder than GTZ. If the fibers are rational they factor into more linear forms, which makes the pattern longer. With 4 squares, two functions on a rank-positive elliptic curve would need simultaneous prime values; that is hopeless.
- *Norms.* Values that are norms from `ℤ[ζ₈]` have all odd-exponent primes `≡ 1 (mod 8)` (STANDARD). But `(7/p) = −1` is an inertness condition. Norms from a field `L` detect only primes with a degree-1 place in `L`. For `σ` as above, the fixed field of `⟨σ⟩` is `ℚ(ζ₈)`, which does not separate `σ` from the identity (VERIFIED, elementary Galois theory). Norm-form values also have unboundedly many prime factors, against the cap of six.
- *Verdict.* Not viable.

### R7. Use the CM structure to make the gcd condition automatic

- *Idea.* With `p = a² + b²` (`a` odd), an odd `ℓ | gcd(d₁, d₂)` must divide `a` and `b² + 1`, so `ℓ ≡ 1 (mod 4)`. If every odd prime factor of `a` is `≡ 3 (mod 4)` (for instance `a` prime and `≡ 3 mod 4`), then `gcd(d₁, d₂) = 4` holds automatically (VERIFIED, elementary).
- *What it would replace.* Only the bad-prime sieve (step 6), which is elementary and not a trust leaf.
- *Obstacle.* It would require controlling the Gaussian decomposition of every pattern prime (a Fouvry–Iwaniec-type statement for a pattern), which is far harder.
- *The relaxation `gcd(e₁, e₂) | c_*`.* Raises the in-class density only from 0.848 to 0.877 (§2.2).
- *Verdict.* No gain in trust.

### R8. Change the curve, the contact set or the test

Each of the following is a structural reason why the needed primes cannot come from Dirichlet or
Chebotarev while the architecture (a height bound in terms of odd contact primes, and one test group
per prime) stays:

- **At least five contacts.** For a contact set of size `m ≤ 4`, the twists `D y² = ∏(x − c)` have genus ≤ 1 and can have infinitely many points with `M_S` bounded, so no bound `h ≤ H·M^k` exists (STANDARD: positive-rank twists of elliptic curves). Hence every height theorem of this type has at least five contacts. The six-contact theorem H is tied to the specific Shimura-curve cover (Section 4, lines 377–972); changing `𝒞` means reproving H.
- **Simultaneous primes per slope.** A good slope of large height needs at least five values `u − cv` with new primes at the same time (by R6). This is a pattern of true complexity at least 3, beyond Fourier analysis, let alone Dirichlet. So even a single large good slope is a Green–Tao-type object. SPECULATIVE as a statement about all methods, but it holds for every method that produces slopes in a parametrized family.
- **The two-place test.** It requires:
  - (i) `p` split in `K₀`;
  - (ii) ordinary reduction, `p ≡ 1 (mod 4)` for CM by `ℤ[i]`;
  - (iii) non-isomorphic reductions, `(N(d)/p) = −1` (an inertness condition);
  - (iv) `gcd(e₁, e₂) | c_*`.

  Condition (iv) involves the Frobenius element modulo every `ℓ` (an infinite intersection of Chebotarev conditions in the division fields of `y² = x³ − x`), and it holds for every test with a fixed shift `c_*`. A variant with several fixed shifts absorbs only finitely many `ℓ`. A test with a witness shift is circular: `[c n_i]P₀` would need multiplication.
- *Verdict.* Making the hypothesis Dirichlet-level would require a new height theorem, which is outside this task. Even then, the slopes' simultaneous prime conditions would remain.

---

## 5. Ranking and recommendation

| Rank | Route | Removes | Chance | Cost |
| --- | --- | --- | --- | --- |
| 1 | R2 with R1/R3: drop the catalogue, state 22P₂ (or 22P′) | **CAT** outright; the catalogue from 22P | high | construction refactor across the size chain and the multiplication constants |
| 2 | R1/R3 alone: state 22P₂, construction unchanged | nothing (CAT stays for the size chain) | high | one Lean file |
| 3 | R4: Green–Tao 2008 for 22P₂ | the GTZ inverse theorem and the nilsequence estimate (down to Szemerédi plus transference) | low | literature work; formalization still out of reach |
| — | R5–R8 | — | negligible inside the architecture | — |

**Recommendation.** The single most promising step is R2 in the form 22P₂.

1. Replace `FixedPrimePattern` by the two-slope, catalogue-free statement 22P₂ (§2.5). Prove `pattern_slopes` from it, using the fixed slope `−10`.
2. Remove the catalogue from the construction (`N_s = P_s`, `ℓ₀ = 12P_s^{2916}`, `S_b = S_ht`), so that `CatalogueBound` disappears.

Success criterion: the main theorem builds with hypotheses `SixContactEstimate`,
`PoleCompleteness` and `TwoSlopePattern` only, with the same axioms.

Chance: **high**.

- Every mathematical ingredient is VERIFIED (§§1.2, 2.1–2.5), except the routine adaptation of the GTZ argument to 22P₂, which uses the same leaves as now.
- The Lean work is a refactor of constants and of one completeness lemma.
- Alternatively the step can be taken in two parts, step 1 first, keeping the effective-Dirichlet plan as a fallback.
- The cost is fidelity: the polynomial would no longer be the manuscript's literal `P_*`, and the project lead must decide whether that is acceptable.

For 22P itself the honest conclusion is negative.

- No route found here reduces it to Dirichlet or Chebotarev. The obstruction is structural (§4, R5–R8).
- What the analysis achieves is a much smaller and cleaner hypothesis: a homothetic copy of a 12-point set in the good primes, with the common difference in a fixed class. Its only deep input is the Green–Tao–Ziegler machinery.
- The one possible downgrade, to Green–Tao 2008, hinges on controlling the common difference at the primes up to 324 (R4). I rate it low.
