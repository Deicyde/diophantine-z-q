# rv-nt22p-red report: counterexamples and edge cases for Lemma P, the modified `q`, and Proposition AP

Full report: `docs/research/rv-nt22p-red.md`. Scripts and outputs: `scratch/rv-nt22p-red/`
(log: `log.md`).

## Verdict

**Proved as written**, for the part in scope: Lemma P (nt-22p §3.2), the modified weak-approximation
choice of `q`, field 2′, and Proposition AP (§3.3). Together these give "22P_AP ⟹ slope
representation with fields 1, 2′, 3, 4 ⟹ the slope predicate is complete at true triples". I found
no counterexample and no gap. Proposition D and the Green–Tao step (§3.4) were not examined
(UNCHECKED here), apart from an independent count of good primes, which agrees.

## What was tested (independent implementation, not reusing scratch/nt-22p)

- Slope data `R₀, a, R`, the tests `C_{gj}`, `W_g`, `Θ` and `B = R/Θ²`, computed from the manuscript
  and Lean definitions. The model is `S_b = S_ht ∪ {331, 337}` with the exact
  `ℓ₀ = 12·P_s^2916·331^732·337^732`. `q` is built by weak approximation with Hensel residue targets
  at the pole primes (about 391,000 digits). `v_p(B)` is computed by PARI `p`-adics with precision
  tracking, and `B` itself by mpmath.
- About 150 inputs in batches of at most 30:
  - Lemma P locally: `ℓ = 2`, `e = 1..5`; `S₀` primes up to `e = 40`; `S_b ∖ S₀`; several primes at
    once; `F < 0` controls.
  - Deep poles: up to `2¹⁵⁰3¹³⁰5¹⁴⁰13²⁰⁰`.
  - Lemma P(3) with `v_ℓ(ℓ₀) = 0`.
  - **10 genuine instances of the Prop AP pattern** (all 11 or 12 values good slope primes), with
    `v` divisible by `2¹⁰, 3⁵, 5⁵, 7⁵, 13⁵, 331²`, at `A = −70, −69` (both sides of the sign-case
    change) and `A = −40`.
  - 13 pseudo-instances with poles up to `2²⁰⁰`, `13¹⁵⁰`, `7¹⁵⁰`.
  - The sign step for 28 values of `A`.
- For every input that satisfies the hypotheses, every PC condition holds: `v_ℓ(B) ≥ 4` on `S₀`,
  `v_p(B) = 1` at the selected primes, the reduced denominator is a square, and `0 < B < 1/2`. The
  controls fail exactly as predicted: with the old `q`, `v₃(B) ≈ 18E₃ − 366e`, negative from
  `e = 144` on (observed −2390 at `e = 150`, −20690 at `e = 200`).

## Findings (none blocking)

| # | Severity | Finding |
| --- | --- | --- |
| F1 | minor | §3.3 remark 1: `K_A ≈ |A| + 71` is wrong. Correct: `K_A = A + 130` for `A ≥ −69`, and `|A| − 8` otherwise. No consequence. |
| F2 | minor | For `v₂(v) ∈ {1, 2}`, `R₀` is **never** a square in `ℚ₂` (nt-22p says "often"); the unit part is `≡ 3, 7` or `5 (mod 8)`. So `e ≥ 3` is sharp. Harmless: field 2 covers `e ≤ 4`. |
| F3 | remark | `F(t) > 0` is needed only at `ℓ = 2` and `ℓ ≡ 3 (mod 4)`. For `ℓ ≡ 1 (mod 4)` Lemma P holds with `η = −1` too (checked at 5 and 13; it fails at 2, 3, 7). |
| F4 | remark | Lemma P's coprimality hypothesis is automatic, from `ℓ | v` and `gcd(u, v) = 1`. |
| F5 | remark | With the true `ℓ₀`, the old `q` already handles poles with `e ≤ 126` at `S₀` (proof), or `e ≤ 143` (computation, unit tests). Lemma P is needed only for deeper poles, which Prop AP produces for large `|A|`. |
| F6 | remark | `N = 23e + v(12) + 2` is sufficient but not sharp (threshold `v(a) ≈ 20.3e − E_ℓ`); Lemma P(3) works even with `E_ℓ = 0`. |
| F7 | cosmetic | "Two remarks" lists three. |

## Suggestions

1. Fix F1 and F2 in the text, and optionally weaken the hypotheses of Lemma P (F3, F4).
2. Add two formal obligations to nt-22p §5 Route 1:
   - `pole_input_valuations` derives `q ≠ 0` from `v_p(q) ≥ C_p` on `S_b`, which the new `q`
     violates at pole primes;
   - its first conclusion `v_p(B) ≥ 103C_p + 8` on all of `S_b` becomes false: at pole primes, and at
     deep poles outside `S₀` under Remark 3, where `v_p(B)` is negative and even, as observed. Only
     the `S₀` conclusion and the square denominator are consumed, so weaken or drop the first
     conclusion.
3. From the counterexample side, the route is ready for formalization (nt-22p Route 1).
