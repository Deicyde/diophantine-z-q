# Hypothesis audit (task hypothesis-audit)

I audited the trust boundary: `ZInQ.FrozenTarget` and the five hypotheses H, PC, MW, 22P and CAT.
I compared each against `diophantine_zq.tex` and against every place the manuscript applies it.
**Verdict: every statement is correct as written.** No statement or article needed a change.
`FrozenTarget` is untouched, `python3 scripts/check_target.py` passes, and `lake build ZInQKernel`
succeeds. I added lemmas that rule out the Lean junk-value pitfalls, plus sanity theorems; they are
listed below.

## Status table

| Article | Lean name | Status |
| --- | --- | --- |
| blueprint/roadmap/main/frozen-target.md | `ZInQ.FrozenTarget` | statement audited, correct (unchanged) |
| blueprint/roadmap/main/six-contact-estimate.md | `ZInQ.SixContactEstimate` | statement audited, correct (unchanged) |
| blueprint/roadmap/main/pole-completeness.md | `ZInQ.PoleCompleteness` | statement audited, correct (unchanged) |
| blueprint/roadmap/main/mordell-weil.md | `ZInQ.MordellWeilE` | statement audited, correct (unchanged) |
| blueprint/roadmap/main/prime-pattern.md | `ZInQ.FixedPrimePattern` | statement audited, correct (unchanged) |
| blueprint/roadmap/main/catalogue-bound.md | `ZInQ.CatalogueBound` | statement audited, correct (unchanged) |

These are hypotheses (`def … : Prop`), so "proved" does not apply. There are no `sorry`s in my
files.

## Statement corrections

None. No article was edited.

## Checks made, with verdicts

### FrozenTarget (`thm:target`, Theorem 1.1)
- Variable count `Fin 292890231905` = `X_0 … X_292890231904`; witnesses `Fin 292890231904`;
  `Fin.cons q w` puts `q` at index 0. **OK.**
- `hyperoperation 4 2 n` is `2↑↑n` with `2↑↑1 = 2` (the manuscript's `\tw`). Tested in Lean:
  `hyperoperation 4 2 3 = 16` and `hyperoperation 4 2 4 = 65536` (`simp [hyperoperation]`). **OK.**
- Coefficient bound `(P.coeff m).natAbs < 2↑↑8` is `|[X^α]P| < 2↑↑8`; degree is `totalDegree`;
  evaluation is `eval₂ (Int.castRingHom ℚ)`; the right side `∃ z : ℤ, (z : ℚ) = q` is ordinary ℤ.
  **OK.** `check_target.py` passes.

### H, the six-contact estimate (`thm:height`, lines 377–404)
- Constants checked symbol by symbol against the display: `F₀ = 324!`, `D = F₀·3^(256F₀⁴)`,
  `G₀ = 116064000000` (digit count checked), `E₀ = 10(DG₀)²`, `Q_R = R^(R E₀)` (rpow, `R ≥ D > 0`),
  `B_cm = D²·3^(21000D²)+1`, `C_cm = 2B_cm + 4096(1028+5D+84000D²)`,
  `H₆ = 2·10¹³·max(1, C_cm, Q_R¹⁷)` (`^17` is a natural power). None of them uses natural
  subtraction or division. **OK.**
- Domain: `S` is a finite set of primes containing every prime ≤ 324. `R` is any real with
  `R ≥ D`, `R ≥ max S`, `R ≥ 10¹²`; the manuscript allows any larger `R` ("every permitted larger
  R", end of the proof). `u ∉ 𝒞`. The quantifier order is ∀S ∀R ∀u. **OK.**
- `h(a/b) = log max(|a|, b)` uses `Rat.num`/`Rat.den` (reduced form, `den > 0`). `|num|` handles
  negative `u`; Lean test: `(-3/2 : ℚ).num = -3`. **OK.**
- `M_S(u)`: in principle a junk value could arise from `padicValRat p 0 = 0` or from
  `primeFactors 0 = ∅`. Neither happens: `u ∉ 𝒞` makes every `u - c ≠ 0`. I proved the
  characterization `prime_dvd_contactSupport_iff`: a prime divides `contactSupport S u` iff
  `p ∉ S` and `v_p(u-c)` is positive and odd for some `c ∈ 𝒞`. The definition is a product over a
  finset of distinct primes. Together these show `contactSupport S u` is exactly the manuscript's
  `M_S(u)`. Negative valuations are excluded, as the manuscript says. **OK.**
- Applications:
  1. Bridge (`lem:test`, `Val`, `eq:close-sound`) uses `H₆(S_ht)|κF(n)|²⁴` with
     `S_ht = {p ≤ 324}` and `R = max(D, 323, 10¹²) = D`. Lean instance: `R = heightD`.
  2. Compiler (§ compiler) uses the exponent `A_ht^(0) = H₆(S_ht)`, the same instance. `Q_D` is a
     natural power because `D·E₀ ∈ ℕ` (`Real.rpow_natCast`).
  3. Multiplication (`prop:box`) uses `S_mul = S_ht ∪ 𝓗 ∪ supp(c_*)` and
     `R = max(D, H_max, c_*, 10¹²) ≥ max S_mul`, with `M^{25} ∣ f ⇒ h(t) ≤ A_ht|f|^{24/25}`.

  All three are covered. Lemma 1.2 ("the constants used by the precision computation and,
  separately, by multiplication") is covered by the ∀S ∀R form. **OK.**
- Not stronger than proved: the statement is Theorem 4.1 verbatim, including the real `R`. **OK.**

### PC, pole completeness (`hyp:PC`, lines 973–1018)
- `polePoly` checked term by term: `m`, `A = mB`, `H = A(A-B²)`, `T₁`, `T₂`, and
  `Q_pole = B(Σ(b_i²-b_i)² + (eHzw-1)² + (r₁²-T₁)² + (r₂²-T₂)²)`, with witnesses
  `b₀..b₅, e, z, r₁, r₂, w`. It contains no division. **OK.**
- `S₀ = {2,3,5,7,13}`; `4 ≤ padicValRat p B` with `B > 0`, so the `padicValRat p 0` junk value
  cannot occur. **OK.**
- `IsSquare B.den` is over ℕ (`∃ r, den = r*r`) on the reduced positive denominator. Lean tests:
  `IsSquare (3/4 : ℚ).den`, `¬ IsSquare (1/2 : ℚ).den`, `(-3/12 : ℚ).den = 4`
  (`decide +kernel`). The inequalities `0 < B < 1/2` are strict in both the manuscript and Lean.
  **OK.**
- Applications:
  1. Multiplication completeness (end of § mult): `v_p(R/Θ²) ≥ 103C_p+8 ≥ 4` on `S_b ⊇ S₀`,
     square denominator, `R/Θ² → 0⁺`.
  2. Bridge `lem:test-complete`: valuation ≥ 4 at 2 and ≥ 6 at the other primes of `S₀`, square
     denominator, `0 < B_pole < 1/2`.

  Both supply exactly these hypotheses, with `B ∈ ℚ`. `lem:pole` (the converse direction) is not
  part of PC; it is elementary and must be proved in Lean. **OK.**

### MW (`prop:generator`, Section 3)
- `K0 = QuadraticAlgebra ℚ 2 0` (`ω² = 2`) is a field via the `Fact (¬ IsSquare 2)` instance.
  `genD = ⟨75, -53⟩ = 75 - 53s`.
- `-genD ^ 2` parses as `-(genD²)`, not `(-genD)²` (checked with `pp.parens`). This matters:
  `y² = x³ + d²x` would be a different curve. `a₄ = -11243 + 7950 s` matches the manuscript's
  `A = (-11243, 7950)` (§ app:literal). **OK.**
- The manuscript uses Mordell–Weil only in "Mordell–Weil now gives rank one". Finite generation of
  `E(K₀)` (`AddGroup.FG genCurve.toAffine.Point`, zero included) plus `[E:2E] = 8` and
  `|E_tors| = 4` gives rank one. The hypothesis is the classical theorem, true because `d ≠ 0`
  makes the curve nonsingular. Every other use of "Mordell–Weil" in the manuscript (lines 1796,
  3905, 3976, 7693) is about the curves `E_ℓ/ℚ` inside the proof of PC/RC, so MW does not cover
  them and does not need to. **OK.**

### 22P, the fixed prime pattern (`prop:fixed-prime-pattern`, lines 1267–1300)
- `𝓑 = [0,-15,-20,-24,-30,-60,1]`; values `v, u_j - b v` with `u₃ = Av - u₁ - u₂`. Lean test:
  `patternValues 5 1 2 3` has length 22, and its explicit contents were checked by `rfl`. **OK.**
- `P_s = primorial 324` is the product of the primes `≤ 324`; `W = 4P_s`. `primorial 324 ^ 4`
  is `(P_s)^4`; `2 ^ W ^ 3` is `2^(W³)` (tested `2^2^3 = 256`). **OK.**
- `Nat.nth` on a finite set gives junk (`0`), which would put `k = 0` in `𝓚` and allow zero
  values. This cannot happen. I proved `infinite_catalogue_class` (Dirichlet's theorem, which is
  in Mathlib), `cataloguePrime_spec` (each `cataloguePrime r i` with `r` a unit class is a prime
  `> 324` in class `r`) and `pos_of_mem_catalogueMultipliers`. So `𝓗` and `𝓚` are exactly the
  manuscript's sets, using neither CAT nor 22P. **OK.**
- Good primes: `p ≠ 2 ∧ ∃ r, r² = 2` means `p` splits in `ℚ(√2)`. Good reduction at the two
  places `s ↦ ±r` means `75 ∓ 53r ≠ 0`, since the discriminant `64d⁶` is a unit for odd `p`.
  `pointCount` = affine solutions of `y² = x³ + ax` plus the point at infinity, with
  `a = -(75∓53r)²`. `gcd = 4` and `p ∤ d₁d₂` are as stated. Sanity theorems:
  - `goodPatternPrime_seventeen` (`17 ≡ 1 mod 8`, `≡ 3 mod 7`, counts 20 and 16).
  - `pointCount_seventeen = 20` at `(17, s-6)` and `pointCount_twentythree = 24` at `(23, s-5)`.
    Both match the counts stated in Prop. 3.1.

  The 17/23 counts cannot tell `±d²` apart (17: −1 is a square; 23: supersingular), which is why
  the parse was checked separately. **OK.**
- Quantifiers: ∀A ∈ ℤ, ∀B₀ ∈ ℝ, ∃u₁ u₂ v with `v ≠ 0`; then for each value its own `ε, k, p`
  with `ε = ±1`, `k ∈ 𝓚` and `B₀ < p` (strict). The prime values need not be distinct, as the
  manuscript says. `x = ε * k * p` is elaborated in ℤ. **OK.**
- Application ("Apply this construction to the nine integral homogeneous quantities", line 1714):
  - It needs `t₁+t₂+t₃ = A` with `t_j = u_j/v`, at most six odd-contact primes per slope, and
    `gcd(d₁,d₂) = 4` (for the CRT compatibility `gcd(lcm(M₀,d₁),d₂) ∣ 4M₀`).
  - The valuation bounds `|v_p(R₀)|, |v_p(t-1)| ≤ C_p` need `v_q(k) ≤ 4` for `q ≤ 324` and
    `v_h(k) ≤ 1` for `h ∈ 𝓗`; both follow from `k = d·h`, `d ∣ P_s⁴`, and `h` a prime `> 324`
    (by `cataloguePrime_spec`).
  - It needs `p ∤ k`, `p ∉ S_b`: the consumer takes `B₀ ≥ max 𝓗`.

  All are covered. **OK.** Not stronger than proved: the statement drops the extra facts the
  proof gives (`p ≡ 1 mod 8`, `p ≡ 3 mod 7`, distinct `h_ν`), which only weakens it. **OK.**

### CAT, the catalogue bound (`prop:cutoff`, lines 6272–6361)
- The manuscript gets `ϑ(X;W,a) > X/(2W)`, hence more than 22 primes `≤ X = 2^(W³)` in each unit
  class, none of them `≤ 324` (every prime `≤ 324` divides `W`). Lean asks for ≥ 22 primes in
  `Finset.Ioo 324 (2^(W³))`. The open endpoints do not matter: 324 is not prime and `2^(W³)` is
  not in a unit class. Tested `Finset.Ioo 3 7 = {4,5,6}`. The Lean statement is weaker than what
  the manuscript proves. **OK.**
- Sufficiency: Prop. 12.1 uses only `H_max < X` and `H_cat ≤ X^{22W}`. I proved
  `cataloguePrime_lt_of_catalogueBound` (CAT ⇒ every `cataloguePrime r i < 2^(W³)` for `i < 22`),
  and `H_cat ≤ X^{22φ(W)}` follows at once. The rest of the proof (`M₀`, `R = D`, `T`) uses
  reduction orders, not the catalogue. **OK.**

## Lemmas added beyond the leaves

All sorry-free and in `namespace ZInQ`:
- `ZInQKernel/Hypotheses/Height.lean`: `dvd_num_natAbs_of_padicValRat_pos`,
  `prime_dvd_contactSupport_iff`.
- `ZInQKernel/Hypotheses/PrimePattern.lean`: `infinite_catalogue_class`, `cataloguePrime_spec`,
  `pos_of_mem_catalogueMultipliers`, `pointCount_eq_card`, `pointCount_seventeen`,
  `pointCount_twentythree`, `goodPatternPrime_seventeen`, `cataloguePrime_lt_of_catalogueBound`.

The kernel checks the point counts by `decide` on `Finset.filter` over `ZMod p × ZMod p` (289 and
529 elements; a few seconds). There is no `native_decide`.

## Problems

- None in the statements.

## Suggestions for the next agent

- **MW may be provable now.** Mathlib v4.35.0 has `AddCommGroup.fg_of_descent'`
  (`Mathlib/GroupTheory/Descent.lean`) and `WeierstrassCurve.Affine.approx_parallelogram_law`
  (`Mathlib/NumberTheory/Height/EllipticCurve.lean`). The mordell-weil-from-descent note
  (`af_8840c820a588a8783b887fbf`) plans to prove `MordellWeilE` from these and the descent index
  `[E:2E] = 8` already needed in Prop. 3.1. That would remove MW from the trust boundary.
- The size chapter's `ZInQ.Syntax.cataloguePrime W B r j` (note `af_ac3ae5e…`) uses
  `p % W = r % W`. For `W = catalogueModulus`, `B = 324` and `r < W` it equals
  `ZInQ.cataloguePrime r j`, since `Nat.mod_eq_of_lt` makes the predicates agree. Prove that
  bridge once and reuse `cataloguePrime_spec` and `cataloguePrime_lt_of_catalogueBound`.
- Consumers of 22P should take `B₀ ≥ max(324, H_max)` to get `p ∤ k` and `p ∉ S_b`. Use
  `pos_of_mem_catalogueMultipliers` to see that every pattern value is nonzero, so no slope lies in
  `𝓒 ∪ {1}`.
- Consumers of H should use `prime_dvd_contactSupport_iff` instead of unfolding `contactSupport`.
  With `M_S(t) ∣ κF(n)` (bridge) or `M_S(t)^25 ∣ f` (multiplication) it gives the needed
  `M_S(t) ≤ |κF(n)|` bounds.
- Trust-boundary remark, not a gap in the hypotheses: these deep inputs fall outside the five
  hypotheses and must still be proved in Lean:
  - formal-group logarithm facts (Silverman IV.5–6);
  - injectivity of torsion into reductions (VII.3.1) and finite index of formal neighbourhoods
    (VII.6.3);
  - for the precision polynomial, the universal halting polynomial (S23), unless the Lean compiler
    replaces it.

  Prop. 12.1 cites Hasse's bound, but the trivial bound `#E(F_q) ≤ 2q+1 < p³` (for `q ≤ p²`,
  `p ≥ 3`) suffices there. Hasse is needed only inside the proof of 22P, which is a hypothesis.
