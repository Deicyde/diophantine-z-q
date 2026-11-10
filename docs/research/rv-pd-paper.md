# Referee report on `pd-paper.md`: positive density of the good slope primes

Subject: `docs/research/pd-paper.md` (2026-11-09), which claims a complete proof of Theorem D (positive
lower Dirichlet density of a subset `G*_L` of the good slope primes) and of Proposition 5.3 (Dirichlet
density implies positive relative upper natural density). Together they give
`PrimesRelUpperDensityPos {p | GoodSlopePrime p}`, which is `ZInQ.GoodPrimeDensity`.

## Verdict

**Proved as written.** I checked every step of §§1–5 myself, recomputed the description of §1 for all
primes below `3·10⁴` with an independent program, and recomputed every explicit constant of §§4–5. I
found no mathematical gap. The one external input, PrimeNumberTheoremAnd's
`SelbergSieve.selberg_bound_simple`, has exactly the statement the note uses. Its source files compile
unmodified against the pinned Mathlib, and the theorem depends only on the standard axioms. The sieve
data of §4.3 can be built as a Mathlib/PrimeNumberTheoremAnd `SelbergSieve`. I proved every field of that
structure in Lean, and `selberg_bound_simple` applies to it verbatim.

All findings are minor. They concern the Lean plan (§6), stale references and one inaccurate side remark
(§4.6) that the proof does not use. None of them changes a constant or a hypothesis of the argument.

Constants confirmed: `A₁ = 16003`, `N₁ = e^{1920}`, `log L ≥ 15A₁ = 240045` (so `L = e^{240045}` works),
`δ_L ≥ 3/(8(L − 1))`, `α_L ≤ 4 log 4·A₁/(L log L) < 5.55A₁/(L log L)`.

## 1. Step-by-step record

Each step carries one mark. CORRECT means checked by me, by hand and, where stated, by computation.
GAP means missing or wrong. UNCHECKED means not examined.

### §1 The character-sum description

| Step | Mark | Comment |
| --- | --- | --- |
| 1.1 Reading of `GoodSlopePrime` and `pointCount` | CORRECT | Matches `ZInQKernel/Hypotheses/PrimePattern.lean` literally: `p.Prime`, `∃ r, r² = 2`, `75 ∓ 53r ≠ 0`, `Nat.gcd` of the two counts `= 4`, with `pointCount p a = Nat.card{y² = x³ + ax} + 1`. `dd̄ = 5625 − 2·2809 = 7`. |
| Lemma 1.1 (point count) | CORRECT | `#{y : y² = c} = 1 + χ(c)` for odd `p` (Mathlib `quadraticChar_card_sqrts`, hypothesis `ringChar ≠ 2`). |
| Lemma 1.2 (scaling) | CORRECT | `(kX)³ + k²a·kX = k³(X³ + aX)`, `χ(k³) = χ(k)`. |
| Lemma 1.3 (shifted products) | CORRECT | Möbius bijection `𝔽_p ∖ {−β} → 𝔽_p ∖ {1}`. True only for odd `p`; see F1. |
| Lemma 1.4 (Jacobsthal) | CORRECT | Recomputed the second moment `Σ_a φ_p(a)² = 2p(p − 1)`, the evenness (`x ↦ −x`, `χ(−1) = 1`), `φ_p(0) = 0` and the square-class step. |
| Lemma 1.5 (`4 ∣ pointCount p (−D²)`) | CORRECT | Recomputed `g(−D²/x) = (D/x)⁴·g(x)`. The roots `±D` are swapped by `τ` and are not in `X`. The fixed points `±iD` are both in `X` or both outside, since `g` is odd and `χ(−1) = 1`. Mathlib `Equiv.Perm.card_fixedPoints_modEq` (for `f : Function.End α` with `f^(p^n) = 1`) applies with `p = 2`, `n = 1`. |
| Prop. 1.6 (1)–(2) | CORRECT | `χ(id)χ(id̄) = χ(−7) = χ(7) = (p/7) = −1` (Mathlib `exists_sq_eq_prime_iff_of_mod_four_eq_one` with `q = 7`). The two counts are `p + 1 ± φ_p(1)`, one of each sign. `φ_p(1) ≡ 2 (mod 4)`. The pair is the same for both roots `±r`. |
| Prop. 1.6 (3), gcd formula | CORRECT | `v₂(g) = 2`, because `4 ∣ g ∣ 2(p + 1)` and `p ≡ 1 (mod 8)`. Odd prime powers divide `g` iff they divide `c_p` and `p + 1`. |
| Prop. 1.6 (4), bad `ℓ ≡ 1 (mod 4)` | CORRECT | `e_p² = p − c_p² ≡ −1 (mod ℓ)` (Mathlib `ZMod.exists_sq_eq_neg_one_iff`). |
| Lemma 2.1 (`G*_L ⊆ G`) | CORRECT | |

*Independent computation* (my own implementation, which counts the points literally from a table of
square roots and does not use the character-sum formula). All 403 primes `p < 3·10⁴` with `p ≡ 1 (mod 8)`
and `p mod 7 ∈ {3, 5, 6}`, with both roots `r` (806 pairs), satisfy: `c_p` is odd, `p = c_p² + e_p²`,
the two counts are `{p + 1 − 2c_p, p + 1 + 2c_p}`, and their gcd is `4·gcd(c_p, p + 1)`. There is no
failure. The literal predicate `GoodSlopePrime` holds for exactly 347 of the odd primes below `3·10⁴`,
and this set equals "class and `gcd(c_p, p + 1) = 1`". Every odd prime dividing some `gcd(c_p, p + 1)` is
`≡ 1 (mod 4)`. The sanity values of §6.2 hold: `c₁₇ = −1` and `c₄₁ = −5`.

### §§2–3 The main term

| Step | Mark | Comment |
| --- | --- | --- |
| Conditions are congruences | CORRECT | `p ≡ 1 (mod 8)` together with `(p/7) = −1` is a Frobenius condition in `ℚ(i, √2, √7) = ℚ(ζ₈, √7)`, which contains `√−7`. For `p ≡ 1 (mod 4)`, `(7/p) = (p/7)`. All further conditions defining `C_L` are congruences modulo `M_L`. |
| §2.3 (the field `K₁`, group `D₄`) | CORRECT | Not used by the proof. The argument that `d` is not a square in `ℚ(√2, √7)` (norms `7` and `1/7`) is right. |
| `δ_L = (1/8)∏(ℓ − 2)/(ℓ − 1) ≥ 3/(8(L − 1))` | CORRECT | CRT count. The telescoping product over the integers `5 ≤ n ≤ ⌊L⌋` equals `3/(⌊L⌋ − 1)`. |
| Units | CORRECT | Every `a ∈ A_L` is a unit mod `M_L` (odd, nonzero mod 7 and mod each `ℓ ∈ Q_L`). This is the hypothesis `IsUnit a` of the Mathlib lemma. |
| Mathlib statement | CORRECT | `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean:348`) is exactly as quoted: `[NeZero q]`, `IsUnit a`, `∃ C, ∀ x ∈ Ioc 1 2, φ(q)⁻¹/(x − 1) − C ≤ ∑' n, residueClass a n / n^x`. |
| Lemma 3.1 | CORRECT | The sum over `a ∈ A_L` is a finite sum of summable `tsum`s, since `x > 1`. Prime powers contribute at most `K₀ = Σ_p log p/(p(p − 1)) = 0.75537…`, which I recomputed. See F5 for the Lean form. |

### §4 The primes removed at `ℓ > L`

| Step | Mark | Comment |
| --- | --- | --- |
| §4.1 (why trivial counts fail) | CORRECT | Heuristic, not used. |
| Prop. 4.1 (lattice count) | CORRECT | `c_p = ℓU` with `1 ≤ \|U\| ≤ √N/ℓ`, and `e_p` in two classes mod `ℓ` within `[−√N, √N]`. Product `(2√N/ℓ)(4√N/ℓ + 2)`. The sum over `ℓ > N^{1/4}` is at most `8N/(N^{1/4} − 1) + 4√N(1 + ½ log N) ≤ 20N^{3/4}` for `N ≥ 10³`. The count is zero for `ℓ > √N`. |
| §4.3 set-up | CORRECT | `F(U, V) ≥ 1`, because `ℓ ∤ b`. `I₂` is an interval, and `M₁, M₂ ≤ 2T/ℓ + 1`. `p ↦ (c_p/ℓ, (e_p − b)/ℓ)` is injective with image in `ℬ`, since `\|c_p\|, \|e_p\| ≤ √p ≤ T`. In (4.1), a prime `p > w` is coprime to `P`. |
| Sieve data versus `BoundingSieve` / `SelbergSieve` | CORRECT | Mathlib's fields are `support : Finset ℕ`, `prodPrimes` squarefree, `weights ≥ 0`, `totalMass`, `nu` multiplicative with `0 < nu p < 1` for `p ∣ prodPrimes`, and `level ≥ 1`. Mathlib defines `multSum d = Σ_{n ∈ support, d ∣ n} weights n`, `rem d = multSum d − nu d·totalMass` and `siftedSum = Σ_{n ∈ support, Coprime P n} weights n`. The note's data meet every field. I built the instance in Lean (§3 below). |
| `selberg_bound_simple` | CORRECT | PrimeNumberTheoremAnd (tag `v4.35.0`, `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean:435`): `siftedSum ≤ totalMass/selbergBoundingSum + Σ_{d ∣ P} (if (d : ℝ) ≤ level then 3^{ω(d)}·\|rem d\| else 0)`. Here `selbergBoundingSum = Σ_{l ∣ P} (if l² ≤ level then g l else 0)` and `g = nu.pmul (prodPrimeFactors (1 − nu p)⁻¹)`, so `g(q) = ν(q)/(1 − ν(q))`. The theorem has no hypotheses beyond the structure. It needs neither complete multiplicativity nor all small primes in `P`. |
| Lemma 4.3 (`ρ(q) = 2q − 1`) | CORRECT | Two lines through `0` over `𝔽_q`, `q ≡ 1 (mod 4)`, `q ≠ ℓ`. Also checked by enumeration for `q < 120` and `ℓ ∈ {5, 13, 17, 29}`. |
| Lemma 4.4 (remainders) | CORRECT | Each residue class meets an interval of `M` integers in `M/d + θ` points, `\|θ\| ≤ 1`, and `ρ(d) ≤ 2^{ω(d)}d`. On real boxes (`N ≤ 10⁸`, `d ≤ 1105`) the largest observed ratio `\|R_d\|/(2^{ω(d)}(M₁ + M₂ + d))` is `0.049`. |
| Error term | CORRECT | `6^{ω(d)} ≤ d²`, since every prime factor is `≥ 5`. There are at most `y` terms, so the sum is at most `y³(M₁ + M₂ + y)`. Since `T/ℓ ≥ N^{1/4} ≥ max(2, y)`, `M₁ + M₂ + y ≤ 6T/ℓ`. With `ℓ ≤ N^{1/4}` this gives `6N^{−1/10} log N ≤ 1` for `N ≥ 10³⁰`. |
| Total mass | CORRECT | `(1 + N^{−1/4}/2)² ≤ 5/4` for `N ≥ 324`. |
| Lemma 4.5 | CORRECT | `g(q) = (2q − 1)/(q − 1)² ≥ 2/q`. The `l ∣ P` with `l² ≤ w²` are exactly the `l ∈ 𝒟` with `l ≤ w` and `ℓ ∤ l`. Terms with `ℓ ∣ l` are at most `(2/ℓ)S₀(w)`. So `S ≥ (3/5)R(w)/V`. Exact computation of `S` for `w ≤ 10⁵` and `ℓ ∈ {5, 13, 101, 997}`: the margin over the bound is at least `1.02`. |
| Claim A | CORRECT | `\|E(t)\| < log(1 + 1/n) ≤ 1/n ≤ 2/t`. The Mathlib lemmas give `H_n − log(n + 1) < γ < H_n − log n` for `n ≥ 1`. `S₁ ∈ [2/3, 1]` and `S₂ ∈ [−(log 3)/3, 0]` (alternating, with decreasing terms from `d = 3`). Numerically, `min_w (R(w) − (2/3)log w + 2) = 2.77` over the tested `w ≤ 10⁶`. |
| Claim B | CORRECT | Prime-power comparison: equality except `r(q^{2j+1}) = 2j + 2 ≤ 2(2j + 1)`. `V ≤ 2ζ(2)⁴ = 14.64` by the lcm count. Checked `r ≤ h ∗ v` for `n < 2·10⁴`. Partial sum `V(10⁶) = 2.74`, and `max R/S₀ = 2.43`. |
| Prop. 4.2 constants | CORRECT | `(log N/60 − 2)/25 ≥ log N/1600` iff `log N ≥ 1920`. `5·1600 + 1 = 8001`, two roots, `2N^{1/40} ≤ N/(ℓ² log N)`. |
| §4.6 (alternatives to the sieve) | CORRECT in conclusion, inaccurate in one detail | See F4. Not used by the proof. |

### §5 Assembly

| Step | Mark | Comment |
| --- | --- | --- |
| Lemma 5.1 | CORRECT | Dyadic blocks and `θ(x) ≤ x log 4` (Mathlib `Chebyshev.theta_le_log4_mul_x`, for `x ≥ 0`). Checked for `L` from `2` to `10⁵`. |
| Lemma 5.2 (Abel summation) | CORRECT | Partial summation with `θ_S(0) = 0`. `θ_S(M)M^{−x} → 0`. `n^{−x} − (n + 1)^{−x} ≤ xn^{−x−1}` and `Σ n^{−x} ≤ x/(x − 1)`. The constant does not depend on `κ` or on `x ∈ (1, 2]`. |
| Prop. 5.3 | CORRECT | Contradiction with `liminf ≥ η > κ`. Mathlib `Chebyshev.eventually_primeCounting_le` is stated for `π ⌊x⌋₊` with real `x`, which specialises to natural `N`. The resulting `c = κ/(log 4 + ε)` can be taken arbitrarily close to `η/log 4`. |
| Theorem D | CORRECT | `T_L ∩ [1, N] ⊆ ⋃_{ℓ > L} Bad_ℓ ∩ [1, N]`. Prop. 4.2 is used for `L < ℓ ≤ N^{1/4}`, `N ≥ N₁`, and Prop. 4.1 above `N^{1/4}`. `liminf(A − B) ≥ liminf A − limsup B`. `3/(8L)` against `5.545A₁/(L log L)` gives the condition `log L > 14.79A₁`. |
| Remark 5.4 and the remarks after Theorem D | UNCHECKED | Not used. |

## 2. Findings

No finding affects the proof of Theorem D or of Proposition 5.3. Severity scale: *major* (the proof
fails), *medium* (a repair is needed before formalising), *minor* (a statement, reference or remark to
correct), *cosmetic*.

**F1 (minor; Lean plan §6.1).** `sum_quadraticChar_shift_mul` is stated without `p ≠ 2`, and it is false
for `p = 2`. In `ZMod 2` with `{α, β} = {0, 1}`, the product `(t + α)(t + β) = t(t + 1)` vanishes for both
`t`, so the sum is `0`, not `−1`. Lemma 1.3 in the text assumes `p` odd, so only the Lean statement is
affected. *Repair:* add `(hp2 : p ≠ 2)`, as `pointCount_eq` already has. `jacobsthal` and
`four_dvd_pointCount` are safe, because `p % 4 = 1` excludes `p = 2`.

**F2 (minor; §6.1 file 7, §7 Route 2, §8 question 1, references).** The note says PrimeNumberTheoremAnd
has only a `v4.34.0` tag and plans to port 1536 lines to Lean 4.35. In fact PrimeNumberTheoremAnd has a
tag `v4.35.0` (commit `127b50e3`). Its `lake-manifest.json` pins Mathlib `56a005855ea1`, which is exactly
our revision, and its toolchain is `v4.35.0`. I compiled `Sieve/AuxResults.lean`, `Sieve/Basic.lean` and
`Sieve/Selberg.lean` from that tag, unmodified, against our Mathlib. They import only Mathlib, Batteries
and each other. `#print axioms SelbergSieve.selberg_bound_simple` reports
`[propext, Classical.choice, Quot.sound]`. *Repair:* replace "port" by "vendor unchanged" (keeping the
Apache-2.0 headers) and answer open question 1. The Route 2 obstacle "pinned to `v4.34.0`" disappears.
`SelbergBounds.lean` is not needed for `selberg_bound_simple`, so file 7 needs 1007 lines, not 1536.

**F3 (minor; §0, §6.1, final link).** The note states the target as `GTSearch.PrimesRelUpperDensityPos`
and closes with `progressions_above_of_greenTaoDense` from a scratch file of another branch. On `main`,
`ZInQKernel/Hypotheses/GreenTao.lean` now defines `ZInQ.PrimesRelUpperDensityPos` (the same definition)
and `ZInQ.GoodPrimeDensity := PrimesRelUpperDensityPos {p | GoodSlopePrime p}`. It already proves
`goodPrimeAP_of_greenTaoDense : GreenTaoDense → GoodPrimeDensity → GoodPrimeAP`. *Repair:* state the
final theorem as `ZInQ.goodPrimeDensity : ZInQ.GoodPrimeDensity` and drop the scratch link.

**F4 (minor; §4.6, not used).** "Brun's pure sieve reaches only `z = (log N)^{O(1)}` and saves
`1/log log N`" understates it. The pure sieve gives an asymptotic for `z` up to
`exp(c log N/log log N)`, and saves a factor `≍ log log N/log N` for this sifting problem of dimension 1.
The conclusion still holds. The resulting per-`ℓ` bound `≪ N log log N/(ℓ² log N)` sums to
`≍ π(N)·log log N/(L log L)`, which is not `O(π(N)/L)` uniformly in `N`. *Repair:* restate the
parameters. The conclusion needs no change.

**F5 (cosmetic; Lemma 3.1, Lean form).** `summable_residueClass_non_primes_div` is the summability at
exponent `1`, of `n ↦ (if n.Prime then 0 else residueClass a n)/n`. Lemma 3.1 needs the prime-power part
at exponent `x ∈ (1, 2]`, bounded uniformly in `x`. In Lean this takes a comparison `n^{−x} ≤ n^{−1}` and
`tsum_le_tsum`. The note's phrase "gives its finiteness, class by class" hides this step. Alternatively,
bound the prime-power part directly by `K₀`, which is uniform in `x` and in the class.

**F6 (cosmetic).** In §4.4 the path should read
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean:435`. That line number is also correct in
`v4.35.0`. The note marks Summary items 2–4 VERIFIED. I confirm them independently (§1 above). The
labels themselves were not relied on.

## 3. Lean checks made for this report

- *Sieve theorem.* As in F2: the three files compile against the pinned Mathlib, and `#check` gives the
  statement quoted in §1 above, with standard axioms only.
- *Instance of the §4.3 data.* I built a `SelbergSieve` with the following data:
  - `support = F(ℬ)` with `F(U, V) = ((ℓU)² + (b + ℓV)²).toNat` on the box
    `[−⌊T/ℓ⌋, ⌊T/ℓ⌋] × {V : |b + ℓV| ≤ T}`, where `T = Nat.sqrt N`;
  - `weights n = #{x ∈ ℬ : F x = n}` and `totalMass = M₁M₂`;
  - `prodPrimes = ∏{q ≤ w : q prime, q % 4 = 1, q ≠ ℓ}`;
  - `nu = prodPrimeFactors (q ↦ (2q − 1)/q²)` and `level = w²`.

  Every field is proved: squarefreeness through `Finset.squarefree_prod_of_pairwise_isCoprime`,
  multiplicativity through `IsMultiplicative.prodPrimeFactors`, and `0 < ν(q) < 1`. The instance depends
  on `[propext, Classical.choice, Quot.sound]`, and `selberg_bound_simple` applies to it with no further
  hypothesis.

## 4. Suggestions for the formalisation

1. **Natural versus real parameters.** The instance above uses a natural `w`. If the formalisation takes
   `w = ⌊N^{1/40}⌋₊`, then `log w ≥ log N/40 − log 2`, and the inequality `S ≥ log N/1600` needs
   `log N ≥ 2370` instead of `1920`. Either raise `N₁` to `e^{2400}`, or filter the primes of `P` by
   `(q : ℝ) ≤ N^{1/40}` and keep `level = N^{1/20}` real (the structure allows a real level). With
   `T = Nat.sqrt N` instead of `√N`, the box still contains every `(c_p/ℓ, (e_p − b)/ℓ)`, and
   `M₁, M₂ ≤ 2T/ℓ + 1` still holds. The error-term inequality `T/ℓ ≥ max(2, y)` has ample slack.
2. **Lemma 4.4 in Lean.** Prove the count for an arbitrary interval of integers and an arbitrary residue
   set `Ω ⊆ (ℤ/d)²`: `|#{x ∈ I₁ × I₂ : x mod d ∈ Ω} − |Ω|M₁M₂/d²| ≤ |Ω|((M₁ + M₂)/d + 1)`. Then apply it
   with `|Ω| = ρ(d)`, using CRT and Lemma 4.3. This keeps the box-geometry separate from the arithmetic.
3. **Keep `UniformBadBound` as the milestone** (§6.2). It isolates file 8 cleanly, and the reduction
   `goodPrimeDensity_of_uniformBadBound` uses only Propositions 1.6 and 4.1, Lemmas 3.1, 5.1 and 5.2, and
   Proposition 5.3. All of them are checked above.
4. The constants have large slack. The data give `#Bad_ℓ·ℓ² log N/N ≤ 0.42` at `N = 2·10⁶` (`ℓ = 5`)
   against `A₁ = 16003`. So any loss from the natural-number conventions can be absorbed by enlarging
   `N₁` and `A₁`, without touching the structure of the proof.

## 5. Computations

All scripts are my own implementations and do not import the note's scripts.

- Description of §1: literal point counts against the character-sum description, for all 403 class
  primes `p < 3·10⁴` and both roots `r`, and literal `GoodSlopePrime` against the prediction for every
  odd prime `p < 3·10⁴`. No mismatch.
- Section 4: local densities `ρ(q)`; remainders on real boxes; Claims A and B; the exact Selberg sum
  `S` against Lemma 4.5; Lemma 5.1; `K₀`; and the counts `#Bad_ℓ` at `N = 2·10⁶`, which agree with
  `2|C|/(ℓ − 1)²` (for example `2331` against `2328` at `ℓ = 5`). The count of class primes bad at some
  `ℓ > N^{1/4}` is `79`, against the bound `20N^{3/4} ≈ 1.06·10⁶`. Every inequality held, with the margins
  quoted in §1.
