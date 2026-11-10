# ap-lean report: route AP in Lean (main theorem under 22P_AP)

Task: the Lean form of route AP of `docs/research/nt-22p.md` (§3.2–3.4). The main theorem now
also holds with the prime-pattern hypothesis replaced by the progression hypothesis 22P_AP, and the
polynomial is unchanged. Every leaf is proved. There is no `sorry`, no new axiom and no
`native_decide`.

- `lake build ZInQKernel`: OK.
- `python3 scripts/check_target.py`: "FrozenTarget matches".
- `#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP`:
  `[propext, Classical.choice, Quot.sound]`.

New modules: `ZInQKernel/Multiplication/Completeness/AP/*.lean`, with root
`ZInQKernel/Multiplication/Completeness/AP.lean` (imported from `ZInQKernel.lean`), and
`ZInQKernel/Hypotheses/PrimeAP.lean`. The only edit to an existing file is `ZInQKernel/Main.lean`:
two imports, one bullet in the module docstring, and the new theorem. No existing statement or
proof was changed.

## Leaves

| Article path (note section) | Lean name | Status |
| --- | --- | --- |
| nt-22p §3.2, Lemma P (hypotheses) | `ZInQ.Mult.PoleAbsorbHyp` (def) | done |
| nt-22p §3.2, Lemma P(1) | `ZInQ.Mult.lemmaP_one` | proved |
| nt-22p §3.2, Lemma P(2) (open set in `ℚ_ℓ`) | `ZInQ.Mult.lemmaP_two` | proved |
| nt-22p §3.2, Lemma P(2) (rational ball; the form used) | `ZInQ.Mult.lemmaP_two_ball`, `ZInQ.Mult.lemmaP_two_rat` | proved |
| nt-22p §3.2, field 2′ | `ZInQ.Mult.GoodSlopeAP` (structure), `ZInQ.Mult.OldBounds` (def) | done |
| field 2 ⇒ field 2′ | `ZInQ.Mult.GoodSlope.goodSlopeAP` | proved |
| nt-22p §3.2, Lemma P(3) | `ZInQ.Mult.lemmaP_three` | proved |
| weak approximation with residue targets | `ZInQ.Mult.weak_approx_targets` | proved |
| pole input valuations under 2′ | `ZInQ.Mult.pole_input_valuations_AP` | proved |
| modified completeness argument | `ZInQ.Mult.slope_complete_AP` | proved |
| slope representation under 2′ | `ZInQ.Mult.SlopeRepresentationAP` (def), `ZInQ.Mult.slopeRepresentationAP_of_slopeRepresentation` | proved |
| completeness consuming SR′ | `ZInQ.Mult.slopes_of_int_AP`, `completeness_core_AP`, `multiply_complete_AP`, `multiplication_exact_AP`, `ZInQ.Assembly.exists_value_relation_iff_AP`, `ZInQ.Assembly.assembly_AP` | proved |
| nt-22p §3.3, hypothesis 22P_AP | `ZInQ.GoodPrimeAP` (def, `Hypotheses/PrimeAP.lean`) | statement (hypothesis) |
| nt-22p §3.3, Proposition AP | `ZInQ.Mult.slopeRepresentationAP_of_goodPrimeAP` | proved |
| main theorem variant | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP` | proved |

## Statement choices and corrections

1. **Lemma P, hypotheses.** `PoleAbsorbHyp ℓ t` uses `u = t.num` and `v = t.den`, so "lowest terms"
   holds by construction. Its clauses are `1 ≤ v_ℓ(v)`, `ℓ = 2 → 3 ≤ v_ℓ(v)`, and `ℓ ∤ u − c v`
   for the seven shifts `patternShifts` (𝒞 ∪ {1}). The note's hypothesis `F(t) > 0` only fixes
   `η = 1`. It is not needed for parts (1) and (2), which are stated for `slopeR0 1 t`. It is
   required where it is used: in field 2′ and in `slope_complete_AP`, which derives `η = 1` from it.
2. **Lemma P(2).** In `ℚ_ℓ`, "`v_ℓ(1 − R₀q²) ≥ N`" is written `‖1 − R₀q²‖ ≤ ℓ^{−N}`. This also
   covers `1 − R₀q² = 0`. The note says "non-empty open set", and `lemmaP_two` proves exactly that.
   The form the completeness proof uses is `lemmaP_two_ball`: a rational centre `m/ℓ^k` and a
   radius `ℓ^{−M}` such that every rational `q` in the ball has `|1 − R₀q²|_ℓ ≤ ℓ^{−N}`.
   The `ℓ`-power denominator of the centre keeps `q` integral at the selected contact primes;
   a centre with an arbitrary denominator would not.
3. **Lemma P(3)** (`lemmaP_three`) is stated as in the note. The tests are integral at every place
   above `ℓ`, `v(R₀) = 2e`, `v(t − 1) = −e`, `v(ℓ₀) ≥ 0`, and `v(a) ≥ 23e + v(12) + 2`; the
   conclusion is `v(B) ≥ 4`.
4. **`pole_input_valuations_AP`** concludes `v_p(B) ≥ 4` on `S_b`, where `pole_input_valuations`
   gives `≥ 103 C_p + 8`. This is all that pole completeness and the square-denominator argument
   use. Its hypothesis at an old prime is: either field 2 holds there and `v_p(q) ≥ C_p`, or the
   hypotheses of Lemma P(3) hold.
5. **Weak approximation** (`weak_approx_targets`) assumes `S ∩ S′ = ∅`; the original lemma did
   not need that, and in the application `S = S_b` and `S′` = the selected primes are disjoint.
   It builds Chinese-remainder idempotents and then reuses `weak_approx_q`.
6. **22P_AP** is stated as the task specifies: `∀ K, ∃ x v : ℕ, 1 ≤ x ∧ 1 ≤ v ∧ ∀ j ≤ K,
   GoodSlopePrime (x + j v) ∧ ∀ q ∈ S_b, q < x + j v`. "Larger than `max S_b`" is written as
   "larger than every element of `S_b`". The docstring is the trust statement: Green–Tao 2008,
   Theorem 1.2, plus Proposition D, with the referee's caveat (see below).
7. **The completeness chain is repeated.** The existing theorems `slopes_of_int` …
   `Assembly.assembly` take `h22 : SlopeRepresentation`, and their statements could not be
   changed. So their five short proofs are repeated with `SlopeRepresentationAP` and
   `slope_complete_AP`; `Assembly.Pstar_spec_of` and `exists_value_relation_iff_of` are reused.
8. **Proposition AP** uses `max S_A⁺ = max(1, A′ + 60)`, `min S_A⁺ = min(−60, A′ − 1)` and
   `K = (max − min).toNat`.

## Lemmas added beyond the leaves (all in `ZInQ.Mult`)

- `LemmaP.lean`: `apContactNum` (def `F(u, v)`), `apContactNum_dvd`, `contactQuot_apContactNum`,
  `PoleAbsorbHyp.not_dvd`, `not_dvd_apContactNum`, `norm_intCast_eq_one_of_not_dvd`,
  `exists_sqrt_apContactNum` (the Hensel step, `hensels_lemma` for `Y² − F(u, v)` at `u³`),
  `PoleAbsorbHyp.num_sub_den_ne_zero`, `eq_num_div_den`, `exists_int_div_pow_near`,
  `norm_one_sub_le_of_near`.
- `GoodSlope.lean`: `GoodSlopeAP.contactQuot_eq_one`, a copy of `padicValRat_contactQuot_eq_one`
  that uses only fields 1 and 3.
- `WeakApprox.lean`: `padicNorm_le_zpow_iff_ap`, `exists_crt_idempotent_ap`,
  `padicNorm_div_pow_mul_le_ap`.
- `PoleValuations.lean`: `padicValRat_traceTheta_of_clear` (`v_p(Θ) = v_p(12)` from the clearing
  inequality; this factors out the shared step of the old part 1). Parts 2 and 3 are copied from
  `pole_input_valuations`.
- `PropAP.lean`: `contactPoly_pos_of_pos`, `contactPoly_pos_of_lt`, `goodSlopeAP_of_progression`
  (fields 1–4 for a slope whose seven numerators are primes above `max S_b`; fields 3 and 4 are the
  argument of `goodSlope_of_primeValues`), `mem_patternShifts_bounds`.

## Referee reports

- `rv-nt22p-proof` and `rv-nt22p-ap` were final when I checked; `rv-nt22p-red` was a draft. None
  reports a gap in Lemma P, the modified completeness argument or Proposition AP. The Lean
  proofs agree with their analysis.
- Points they found wrong in the note, all minor and none affecting the Lean statements:
  - `K_A` is `A + 130` (for `A ≥ −69`) or `−A − 8`, not `≈ |A| + 71`.
  - For `v₂(v) ∈ {1, 2}`, `R₀` is never a 2-adic square (the note says "often"). So `e ≥ 3` at 2
    is sharp.
  - §3.3 announces two remarks and lists three.
  - Green–Tao 2008 prove Theorem 1.2 only in outline (§10). I recorded this caveat in the
    docstring of `GoodPrimeAP`.
  - Szemerédi's theorem enters in finitary form without quantitative bounds.
- Their remarks on redundancy are consistent with the Lean: the seven-numerator hypothesis follows
  from lowest terms (red F4, proof 7). The `red` draft's extra obligation `q ≠ 0` at the pole
  primes is discharged by `weak_approx_targets`, which returns `q ≠ 0`.

## Problems

None blocking. The cost is duplication: the completeness chain (5 short proofs), parts 2–3 of
`pole_input_valuations`, the core of `slope_complete`, and fields 3–4 of
`goodSlope_of_primeValues` are repeated, because the existing statements were frozen.

## Suggestions for the next agent

1. Remove the duplication by restating the old theorems as corollaries of the AP versions:
   `slope_complete` from `slope_complete_AP ∘ GoodSlope.goodSlopeAP`, and `Assembly.assembly`
   from `assembly_AP ∘ slopeRepresentationAP_of_slopeRepresentation`. This needs permission to
   change proofs, not statements, in `Completeness/` and `Assembly/Top/`.
2. Field 2″ (referee suggestion): Lemma P only at `S₀`, and "`v_ℓ(F(t))` even" at `S_b ∖ S₀`. It
   would simplify field 2′, but the present general form already builds.
3. `PoleAbsorbHyp` could drop the seven non-divisibility clauses, which follow from lowest terms
   when `ℓ ∣ den t` (one lemma).
4. Write out Proposition D (route 2 of the note), the density input behind the trust statement of
   `GoodPrimeAP`.
