# rv-nt22p-proof report: referee check of Lemma P and the modified completeness argument

Full report: `docs/research/rv-nt22p-proof.md`. Scope: §3.2–3.3 of `docs/research/nt-22p.md`
(Lemma P, field 2′, the modified choice of `q`, Proposition AP, Remarks 1–3). I checked them
against manuscript lines 1170–1190 and 1700–1758 and against the Lean source (`GoodSlope`,
`slope_complete`, `pole_input_valuations`, `weak_approx_q`, `tests_integral_old`,
`PoleCompleteness`). Proposition D and the application of Green–Tao 2008 are not covered.

## Verdict

**Proved after the listed repairs.** All repairs are minor, and none changes the argument.
Lemma P (1)–(3), the modified completeness argument, Proposition AP and Remark 3 are correct. I
checked each step by hand, and an independent exact computation in `ℚ(√2)` agrees.

## Findings (severity)

1. **Lemma P(1)–(3): CORRECT.** `R₀ℓ^{−2e} = (vℓ^{−e})²u⁶(u − v)^{−8}Π` with
   `Π = ∏(1 − cv/u) ≡ 1 (mod ℓ^e)`, which is a local square for odd `ℓ`, and at 2 once `e ≥ 3`.
   `v(C_{gj}) ≥ −e(k_j − 1)` gives `v(RC²) ≥ 2E_ℓ + 2α − 46e` for `k_j = 25`. For `α ≥ 23e + v(12) + 2`
   this gives `Θ ≡ 12` beyond `v(12)`, so `v_ℓ(Θ) = v_ℓ(12)` (split, inert and ramified `ℓ` all
   work), and `v_ℓ(B) = 2E_ℓ + 2α + 2e − 2v(12) ≥ 46e + 4`. Numerically, 30 of 30 samples with poles
   at all five primes of `S₀` (and `ℓ₀ = 1`, the worst case) satisfy `v_ℓ(Θ) = v_ℓ(12)` and
   `v_ℓ(B) ≥ 4`. A control with `α = 19e` fails at every prime of every sample, so the threshold
   is really used.
2. **Test integrality when `t` has a pole: CORRECT.** The test values `testValues (h g) (z g) c`
   depend only on the shifts and the indices. The hypotheses of `tests_integral_old` are
   `M₀ | h`, `h ≠ 0`, `h ≠ c_*`, `p ∈ S_b`, and none involves `t`. The default shift `2c_*` of
   unused groups satisfies them too.
3. **Prime 2 (minor).** For `e = 1` the unit `R₀2^{−2e}` is `≡ 3, 7 (mod 8)`, and for `e = 2` it
   is `≡ 5`. So with `η = 1`, `R₀` is *never* a 2-adic square (the note says "often"), and
   `v₂(1 − R₀q²) ≤ 2` for all `q`. This is harmless, because `e ≤ 2 < B₂ = 4` falls under field 2.
   Checked exhaustively.
4. **Modified completeness argument: CORRECT.** The real place and `S_pole` require the same
   `η = 1`, which `F(t) > 0` guarantees. `ε` from the positivity lemma does not depend on `q`.
   The five local conditions on `q` are compatible by weak approximation. Selected primes keep
   `v_p(B) = 1`, and every other prime, including the auxiliary one, keeps even valuation,
   independently of `q`.
5. **Proposition AP: CORRECT.** Lowest terms, signs (`t₁ > 1`, `t₂ < −60`), fields 1, 2′, 3 and
   4 all check. Cosmetic: `K_A = A + 130` for `A ≥ −69` and `−A − 8` for `A ≤ −70`, not
   `≈ |A| + 71`.
6. **Remark 3: CORRECT, and can be strengthened.** At `ℓ ∈ S_b ∖ S₀`, `v_ℓ(B) ≡ v_ℓ(F(t)) (mod 2)`
   for every `q`. So field 2 there can be replaced by "`v_ℓ(F(t))` even", with no bound at all;
   `GoodSlope.old` is consumed only in part 1 of `pole_input_valuations`.
7. **Redundant hypothesis (cosmetic).** `e ≥ 1` and lowest terms already make the seven
   numerators `ℓ`-units. The alternative of field 2′ is just
   `v_ℓ(t) < 0 ∧ F(t) > 0 ∧ (ℓ = 2 ⇒ v₂(t) ≤ −3)`.
8. **Lean plan (minor; incomplete).** The note lists three changes. The work that is actually
   needed:
   - a new Lemma P(1)–(2), via `hensels_lemma` for `X² − Π` at `1`, whose hypothesis is exactly
     "`ℓ` odd or `e ≥ 3`";
   - a residue-class variant of `weak_approx_q`, in which the residue depends on the power of the
     auxiliary prime;
   - a second branch in part 1 of `pole_input_valuations`, whose conclusions, including
     `103C_p + 8`, can stay unchanged;
   - the new branch in `slope_complete`;
   - a new `goodSlope_of_progression`. `goodSlope_of_primeValues` cannot be reused, because its
     `hold` hypothesis is what fails for progressions.

   The other changes are one-line `Or.inl` edits in `goodSlope_of_values`,
   `goodSlope_of_primeValues` and `goodSlope_neg_ten`, plus the new hypothesis in `Main`.
   `GoodSlope.old_le_Cp` has no users. The consumers of `SlopeRepresentation` are unchanged.
9. **Observation.** With the real `E_ℓ`, the old argument (with `α = 0`) already absorbs poles
   up to `e ≤ 126` on `S_ht` and `e ≤ 31` on the catalogue. Lemma P is needed only beyond that,
   which a progression from Green–Tao does produce for large `|A|`.

## Suggestions

- Adopt 22P_AP with field 2″: Lemma P at `S₀` only, and parity at `S_b ∖ S₀`. This makes the
  Lean change smaller.
- First Lean test: prove Lemma P(1)–(2) in integer form with `hensels_lemma`, and the
  residue-class weak approximation. Then extend part 1 of `pole_input_valuations` and check that
  the two branches agree for `5 ≤ e ≤ 126`.
- Correct the three statements in the note (finding 3, the constant of `K_A`, and the Lean plan).
