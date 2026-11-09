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
