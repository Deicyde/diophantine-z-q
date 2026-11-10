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
