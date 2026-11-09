# Referee report on nt-22p §3.2–3.3: Lemma P, the modified choice of `q`, and Proposition AP

Focus: counterexamples and edge cases, tested by computation.

Subject: `docs/research/nt-22p.md`, §3.2 (Lemma P and the modified completeness argument) and
§3.3 (the hypothesis 22P_AP and Proposition AP). The density of the good primes (Proposition D),
the application of Green–Tao 2008 (§3.4) and §4–5 are outside this report, except for one count
of good primes (§3.6 below).

Notation as in nt-22p. `t = u/v` in lowest terms, `e = v_ℓ(v)`, `R₀ = ηF(t)/(t − 1)⁸`,
`a = 1 − R₀q²`, `R = ℓ₀²a²R₀`, `C_{gj} = D_{gj}/(R₀^{k_j}(t − 1)^{k_j+1})`,
`W_g = ∏_j(1 + RC_{gj}²)`, `Θ = Tr Σ_g W_g^{−1}`, `B = R/Θ²`. `E_ℓ = v_ℓ(ℓ₀) = 52C_ℓ + v_ℓ(12) + 4`,
which is `2916 + v_ℓ(12)` for `ℓ ≤ 324` and `732` on the catalogue. Pole completeness (PC,
manuscript Theorem 5.2, `ZInQ.PoleCompleteness`) asks: reduced denominator of `B` a square,
`0 < B < 1/2`, and `v_ℓ(B) ≥ 4` for `ℓ ∈ S₀ = {2, 3, 5, 7, 13}`.

## Verdict

**Proved as written**, for the part examined here: Lemma P, the modified choice of `q`, and
Proposition AP, that is, the implication "22P_AP ⟹ every integer is a sum of three slopes
satisfying fields 1, 2′, 3, 4 ⟹ the slope predicate is complete at every true triple". I found no
counterexample and no gap. Every step was checked by hand, and the statements were tested on
independently implemented data (about 120 slope inputs in six batches, including genuine
instances of the 14-point pattern made of good slope primes, with `v` divisible by `2¹⁰`, `3⁵`, `5⁵`,
`7⁵`, `13⁵` or `331²`, and on both sides of the change of sign case at `A = −69/−70`).

The findings below are corrections of detail and remarks. None affects the conclusion. The
largest is a slip in remark 1 of §3.3 (the value of `K_A`). Two are sharpenings: Lemma P's
hypothesis `e ≥ 3` at `ℓ = 2` is sharp (for `e = 1, 2` the number `R₀` is never a square in `ℚ₂`),
and the hypothesis `F(t) > 0` can be weakened at primes `ℓ ≡ 1 (mod 4)`. One remark is about how
much Lemma P buys: with the manuscript's `ℓ₀` the old choice of `q` already clears poles of order
up to about 126 (by the proof) or 143 (in practice) at the primes of `S₀`. So Lemma P is needed only
for very deep poles. Proposition AP produces such poles for large `|A|`, because `v` is then
divisible by high powers of every small prime, so the lemma remains necessary.

The formal obligations listed in nt-22p §5 (a field 2′, a Lemma P branch in
`pole_input_valuations`, a weak approximation with residue targets) are accurate. One more is
needed: `pole_input_valuations` currently obtains `q ≠ 0` from `v_p(q) ≥ C_p` on `S_b`, which the
modified `q` does not satisfy at the pole primes (§4, item 5).

## 1. Findings

| # | Severity | Finding |
| --- | --- | --- |
| F1 | minor (text) | §3.3 remark 1: `K_A ≈ |A| + 71` is wrong. In fact `K_A = A + 130` when `A + 70 ≥ 1` and `K_A = |A| − 8` otherwise. The conclusion of the remark (for large `|A|` every small prime divides `v`) is unaffected. |
| F2 | minor (text) | §3.2 numerical check: "with `v₂(v) ≤ 2`, `R₀` is often not a square in `ℚ₂`". In fact `R₀` is *never* a square in `ℚ₂` when `v₂(v) ∈ {1, 2}` and `F(t) > 0`: the unit part of `R₀2^{−2e}` is `≡ 3` or `7 (mod 8)` for `e = 1` and `≡ 5 (mod 8)` for `e = 2`. The hypothesis `e ≥ 3` of Lemma P is therefore sharp. Harmless, because `e ≤ 4 = B₂` falls under field 2. |
| F3 | remark | Lemma P's hypothesis `F(t) > 0` (so `η = 1`) is needed only at `ℓ = 2` and `ℓ ≡ 3 (mod 4)`. For `F(t) < 0` the same proof works at `ℓ ≡ 1 (mod 4)` (for example `ℓ = 5, 13`), since `−1` is a square in `ℚ_ℓ`. The correct hypothesis is "`ηR₀ℓ^{−2e}` is a square in `ℚ_ℓ`". Proposition AP never needs this (both variable slopes have `F > 0`). |
| F4 | remark | The hypothesis "the seven numbers `u − cv`, `u − v` are prime to `ℓ`" of Lemma P is automatic: `ℓ | v` and `gcd(u, v) = 1` give `u − cv ≡ u ≢ 0 (mod ℓ)`. |
| F5 | remark | With the manuscript's `ℓ₀`, the old choice `v_ℓ(q) ≥ C_ℓ` already gives `v_ℓ(B) ≥ 4` at `ℓ ∈ S₀` for poles of order `e ≤ 126`, by the manuscript's own estimate with `C_ℓ` replaced by `2e`. For test values that are units at `ℓ`, it gives this for `e ≤ 143`, and computation confirms that it fails from `e ≈ 150` on (§3.3). The bound `B_ℓ = 4` of field 2 is far from what the proof needs. Lemma P is needed only beyond this range, which Proposition AP does reach for large `|A|` (F1). |
| F6 | remark | The constant `N = 23e + v_ℓ(12) + 2` of Lemma P(3) is sufficient but not sharp: for unit test values the conclusion holds from `v_ℓ(a) ≳ 20.3e − E_ℓ` (§3.3). Lemma P(3) holds even with `E_ℓ = 0`, which the computation confirms (§3.3, Part B). |
| F7 | cosmetic | §3.3 announces "Two remarks" and lists three. |

No finding is a GAP. Each step's status is in §2.

## 2. Step-by-step check

### 2.1 Lemma P

- **(1) `v_ℓ(R₀) = 2e`, `v_ℓ(t − 1) = −e`.** From `t − c = (u − cv)/v`,
  `R₀ = v²F(u, v)/(u − v)⁸`, and all numerators are `ℓ`-units (F4). CORRECT.
- **(1) `R₀` is a square in `ℚ_ℓ`.** `R₀ℓ^{−2e} = (vℓ^{−e})²(u³)²(u − v)^{−8}∏_c(1 − cv/u)`, and each
  factor `1 − cv/u` is `≡ 1 (mod ℓ^e)`. A unit `≡ 1 (mod ℓ)` is a square for odd `ℓ`, and a unit
  `≡ 1 (mod 8)` is a square in `ℚ₂`. CORRECT. The hypothesis `e ≥ 3` at `2` is sharp (F2), and
  `F(t) > 0` can be weakened at `ℓ ≡ 1 (mod 4)` (F3).
- **(2) The ball.** With `q₀ = ±R₀^{−1/2}`, `1 − R₀q² = −R₀(q − q₀)(q + q₀)`, so
  `v_ℓ(a) = 2e + v_ℓ(q − q₀) + v_ℓ(2q₀)` once `v_ℓ(q − q₀) > v_ℓ(2q₀) = v_ℓ(2) − e`. Hence
  `v_ℓ(a) ≥ N` on a ball. CORRECT.
- **(3) `v_ℓ(B) ≥ 4`.** `v(R) = 2E_ℓ + 2α + 2e` and
  `v(C_{gj}) = v(D_{gj}) − 2ek_j + e(k_j + 1) ≥ −e(k_j − 1)`, so `v(RC_{gj}²) ≥ 2E_ℓ + 2α − 46e` for
  `k_j ∈ {1, 25}`. For `α ≥ N` this is at least `2v_ℓ(12) + 4 > v_ℓ(12)`, so every `W_g^{±1}` is
  `≡ 1` beyond `v_ℓ(12)` at each place above `ℓ`. The trace step holds also at the ramified prime
  `2`: for `x ∈ K₀` with `v_𝔭(x) = m/2` (normalized to extend `v₂`), the different `(2√2) = 𝔭³`
  gives `v₂(Tr x) ≥ ⌊(m + 3)/2⌋ ≥ m/2`. So `v_ℓ(Θ) = v_ℓ(12)` and
  `v_ℓ(B) = 2E_ℓ + 2α + 2e − 2v_ℓ(12) ≥ 46e + 4`. CORRECT. Only `E_ℓ ≥ 0` is used (F6).
- **Integrality of the tests above `S_b`.** `ZInQ.Mult.tests_integral_old`
  (`SbIntegrality.lean:98`) has hypotheses `M₀ | h`, `h ≠ 0`, `h ≠ c_*` and `p ∈ S_b`. It does not
  mention `t`, and `slope_complete` discharges these hypotheses from `exists_shift` independently
  of `t`. CORRECT.

### 2.2 The modified choice of `q`

- **Where field 2 is used.** `GoodSlope.old` is used only in `pole_input_valuations`
  (`PoleValuations.lean:126`). `GoodSlope.old_le_Cp` has no other caller. Field 2 has no consumer
  in the selected-prime analysis, in the shift choice, or in the real-place lemma
  `pole_input_small`. So replacing field 2 by 2′ affects only the `S_b` part of
  `pole_input_valuations`. CORRECT.
- **Compatibility of the local conditions.** The conditions on `q` are: a ball around `±R₀^{−1/2}`
  at each `ℓ ∈ S_pole`, `v_p(q) ≥ C_p` at `p ∈ S_b ∖ S_pole`, `v_p(q) ≥ 0` at the selected primes,
  and `|q − R₀^{−1/2}| < δ` at the real place. They concern distinct places, so weak approximation
  applies. Concretely, `q = m/(∏_{ℓ∈S_pole}ℓ^{e_ℓ}·L^k)` with `L` an auxiliary prime, `m` in a
  residue class modulo `∏ℓ^{N_ℓ+e_ℓ+O(1)}·∏p^{C_p}` (Hensel lifting gives the class), and `m`
  nearest to `R₀^{−1/2}·∏ℓ^{e_ℓ}·L^k`. This is the construction I implemented (§3.1). CORRECT.
- **The other primes.** At `p ∈ S_b ∖ S_pole` nothing changes. At a selected prime `p`, `q` is
  `p`-integral and `v_p(R₀) = 1`, so `a ≡ 1 (mod p)` and `v_p(B) = 1` as before. At every other
  prime, including the auxiliary prime and the primes of `S_pole`'s denominators, `a` enters `R`
  squared, so `v_p(B) ≡ v_p(R₀) (mod 2)`. And `v_p(R₀)` is odd only at odd contact primes (all
  selected) and possibly at primes of `S_b`. CORRECT.
- **Real place.** `W_g ≥ 1` in both real embeddings (`RC² ≥ 0`), so `0 < Θ ≤ 12`, and `B → 0⁺` as
  `a → 0`; `pole_input_small` applies unchanged. CORRECT.
- **`q ≠ 0` in Lean.** The present proof of `pole_input_valuations` derives `q ≠ 0` from
  `v_p(q) ≥ C_p` at `p ∈ S_b` (via `padicValRat 0 = 0`). At `ℓ ∈ S_pole` the modified `q` has
  `v_ℓ(q) = −e ≠ 0`, which again forces `q ≠ 0`, but the derivation must be rewritten. Not a
  mathematical gap; a formal obligation missing from nt-22p §5.
- **Remark 3 of §3.3 (Lemma P needed only on `S₀`).** At `ℓ ∈ S_b ∖ S₀`, for a slope of the
  progression form, `v_ℓ(R₀) = 2e` is even, so `v_ℓ(B)` is even for every `q`, and PC requires
  nothing more there. CORRECT. (Negative even valuations then occur at such `ℓ` if the old `q` is
  kept and `e` is large. This is allowed, and it was observed in the computation, §3.4.)

### 2.3 Proposition AP

- **The fourteen values.** For `c′ ∈ S_A⁺`, `u − c′v = x + (max S_A⁺ − c′)v` with
  `max S_A⁺ − c′ ∈ [0, K_A]`: a term of the progression. For `t₂ = A′ − u/v`,
  `t₂ − c = −(u − (A′ − c)v)/v` and `t₂ − 1 = −(u − (A′ − 1)v)/v`. CORRECT.
- **Lowest terms.** A common prime of `u` and `v` divides `x` and hence every term. CORRECT.
- **Field 1.** The numerators are nonzero primes. CORRECT.
- **Signs.** `max S_A⁺ = max(1, A′ + 60)`. If `A′ + 60 ≥ 1`, then `t₂ = −60 − x/v < −60`;
  otherwise `t₂ = A′ − 1 − x/v < A′ − 1 < −60`. Also `t₁ > max S_A⁺ ≥ 1`. So `F(t₁), F(t₂) > 0`.
  CORRECT, and tested at the change of case (§3.5).
- **Field 2′.** At `ℓ ∈ S_b` all fourteen values are `ℓ`-units, being primes `> max S_b`. If
  `ℓ ∤ v`, both valuations in field 2 are 0. If `e ≥ 1`, then `v_ℓ(t − 1) = −e` and
  `v_ℓ(F(t)/(t − 1)⁸) = 2e`, so field 2 holds iff `e ≤ B_ℓ`. Otherwise `e ≥ B_ℓ + 1`, which is
  `≥ 5` at `2`, and the hypotheses of Lemma P hold. CORRECT.
- **Fields 3, 4.** The odd contact primes outside `S_b` of `t₁` are exactly the six primes
  `u − cv`, with valuation 1. Primes dividing `v` give negative valuations, and no pattern prime
  divides `v`. The same holds for `t₂`. Coincidences `T ∩ (A′ − T) ≠ ∅` (which occur, for example,
  at `A = −70, −40`, where `|S_A⁺| = 11`) only make a prime a contact prime of both slopes, or make
  a contact prime of one slope the prime `u − v` of the other. Each slope has its own groups, so
  nothing changes. CORRECT.
- **The constant slope `−10`.** `t − c ∈ {−10, 5, 10, 14, 20, 50}`, `t − 1 = −11`, and `F(−10) < 0`,
  so `η = −1`; there are no poles and field 2 holds. CORRECT. Recomputed in every instance of §3.5.
- **Remark 1.** The divisibility argument is CORRECT. The value of `K_A` is wrong (F1).
- **The Lean form `GoodPrimeAP`** (`∀ K N, ∃ x v, N < x ∧ 0 < v ∧ ∀ j ≤ K, GoodSlopePrime (x + jv)`),
  applied with `N = max S_b`, gives exactly what the proof uses. CORRECT.

UNCHECKED here (outside this report's focus): Proposition D, and the application of Green–Tao
2008 in §3.4.

## 3. Computations

### 3.1 Implementation

Everything was implemented afresh from the manuscript (lines 1177–1191 and 1705–1758) and the Lean
statements (`GoodSlope`, `poleInput`, `pole_input_valuations`, `slope_complete`,
`weak_approx_q`, `PoleCompleteness`), in Python with PARI/GP 2.17 (`cypari2`), `gmpy2` and
`mpmath`. Scripts: `scratch/rv-nt22p-red/` (`slopelib.py` is the library).

- **Old primes.** `S_b` is modelled as `S_ht ∪ {331, 337}`, with `331` and `337` standing in for
  catalogue primes (`B_p = 1`, `E_p = 732`). The true catalogue contains every prime between `324`
  and `W = 4P_s ≈ 10¹³⁷` (each such prime is the first prime of its own class), so genuine pattern
  primes are astronomically large. The model keeps the local situation at every old prime that
  occurs. The constant `ℓ₀ = 12·P_s^{2916}·331^{732}·337^{732}` (383,613 digits) is used exactly.
- **The witness `q`.** This is the modified weak approximation of §2.2:
  `q = m/(∏_{S_pole}ℓ^{e_ℓ}·L^k)`, with `L = 1000003` (or the next prime avoiding all relevant
  primes) and `m` in the CRT class giving `v_ℓ(1 − R₀q²) ≥ N_ℓ = 23e_ℓ + v_ℓ(12) + 2` at
  `ℓ ∈ S_pole` (the Hensel square root of the unit `(R₀ℓ^{−2e})^{−1}`) and `v_p(q) ≥ C_p` on the rest
  of `S_b`. `m` is the member of the class nearest to `R₀^{−1/2}·∏ℓ^{e_ℓ}·L^k`, and `L^k` is large
  enough that `R·max|C|² < 10^{−40}`. The resulting `q` has about 391,000 digits.
- **Test values.** The model takes six groups of twelve elements of `ℤ[√2]`, integral everywhere,
  either random (coefficients up to `10⁶`) or equal to `1`. A group assigned to a selected prime `p`
  has `D_{gj} = π^{k_j}·(cofactor)` with `π` a generator of a prime of `ℤ[√2]` above `p`. This
  realizes exactly the hypotheses `hD_old`, `hD_sel` of `pole_input_valuations`. Unit test values at
  `ℓ` are the worst case for Lemma P(3).
- **The pole input.** `B` has millions of digits and is never formed. `v_p(B)` is computed from
  exact `t, q, a, R₀, ℓ₀` in PARI's `p`-adic arithmetic with precision tracking: through the two
  embeddings `√2 ↦ ±r` at split `p`, and in `ℚ_p(√2)` at inert or ramified `p`. The real value of
  `B` is computed in `mpmath` from both real embeddings. The square-denominator condition is checked
  at every prime where `v_p(B)` can be odd. Since `v_p(B) ≡ v_p(R₀) (mod 2)` identically, these are
  the primes dividing a numerator or the denominator of `R₀`, all known, together with the auxiliary
  prime. At every other prime `v_p(B)` is even.
- **Genuine pattern instances.** A sieve with PARI `ellcard` (`ap_search.py`) finds `x, v` such
  that all the numbers `u − c′v`, `c′ ∈ S_A⁺`, are good slope primes in the sense of
  `GoodSlopePrime` (point counts of both reductions, `gcd = 4`). Admissibility forces `2, 3, 7, 11 | v`
  for `A = −70`, `2 | v` for `A = −69`, and `2, 3, 7 | v` for `A = −40`.

Checks of the implementation: (i) the old argument reproduces `v_p(B) ≥ 103C_p + 8` on `S_b` for
slopes satisfying field 2; (ii) the controls of §3.3 fail exactly where the theory predicts; (iii) an
independent count gives 1,925 good slope primes below `2·10⁵` (§3.6), as in nt-22p.
