# Task mult-completeness: report

Completeness of the multiplication template (blueprint `multiplication/completeness/`). All Lean
code is in `ZInQKernel/Multiplication/Completeness/` (namespace `ZInQ.Mult`), root module
`ZInQKernel/Multiplication/Completeness.lean`, imported from `ZInQKernel.lean`.
`lake build ZInQKernel` succeeds. No `axiom`, `native_decide`, `implemented_by`, `extern` or
kernel-skipping option was added.

Eight of the nine leaves are proved. `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound` for `pattern_slopes`, `pole_input_valuations`, `tests_integral_old`,
`tests_precision_selected`, `slope_complete` and `completeness_core`. These are sorry-free only after
merging `origin/wip/mult-formal-log`, which proves `ellLog_add`. The final leaf
`multiply_complete` has its final statement and a `sorry` proof: it needs the multiply unfolding
and the height-certificate semantics of task mult-certificate, which are not yet committed (see
Problems).

Merged into this branch: `wip/mult-certificate` (through `e59e0b9`: constants, slope predicate,
tests, constants properties, local templates, guard) and `origin/wip/mult-formal-log`.

## Leaves

| article path | Lean name | status |
|---|---|---|
| multiplication/completeness/pattern-slopes.md | `ZInQ.Mult.pattern_slopes` (with the structure `ZInQ.Mult.GoodSlope`), PatternSlopes.lean | proved |
| multiplication/completeness/shift-choice.md | `ZInQ.Mult.shift_choice` (and `shift_choice'` for the consequences), ShiftChoice.lean | proved |
| multiplication/completeness/sb-integrality.md | `ZInQ.Mult.tests_integral_old`, SbIntegrality.lean | proved |
| multiplication/completeness/weak-approximation.md | `ZInQ.Mult.weak_approx_q`, WeakApproximation.lean | proved |
| multiplication/completeness/pole-input-positivity.md | `ZInQ.Mult.pole_input_small`, PolePositivity.lean | proved |
| multiplication/completeness/pole-input-valuations.md | `ZInQ.Mult.pole_input_valuations` (with `ZInQ.Mult.poleInput`), PoleValuations.lean | proved |
| multiplication/completeness/selected-prime-precision.md | `ZInQ.Mult.tests_precision_selected`, SelectedPrecision.lean | proved |
| multiplication/completeness/slope-completeness.md | `ZInQ.Mult.slope_complete`, SlopeCompleteness.lean | proved |
| multiplication/completeness/completeness.md | `ZInQ.Mult.multiply_complete`, Template.lean | statement only (sorry); mathematical content proved as `ZInQ.Mult.completeness_core` |

## Statement corrections and deviations

- **weak-approximation.** The disjointness of `S` and `S'` is not needed and is dropped. Since
  `padicValRat p 0 = 0`, the conclusion also includes `q ≠ 0`.
- **pattern-slopes.** Conditions 1-4 are the structure `GoodSlope B₀ t`. Condition 4 says there is
  a `Finset P` with `P.card ≤ 6` and `p ∈ P ↔ p ∉ S_b ∧ IsOddContactPrime t p`. The proof
  produces this explicit set, and the completeness proof iterates over it. In condition 3 the
  structure states `∀ c ∈ 𝒞, 0 < v_p(t - c) → v_p(t - c) = 1`. The uniqueness of such a `c` is the
  separate lemma `contact_unique`. The good primes are exactly `GoodPatternPrime`.
- **pole-input-positivity.** As stated, with `R = ℓ² a² R₀`, `W_g = groupW R (C g)` and
  `Θ = traceTheta (fun g => groupW R (C g))` (the certificate's definitions). `ε` is a real.
  `pole_input_small_R` is the same statement in terms of `R` (`0 < R < ρ`).
- **pole-input-valuations.** Stated for any rational `ℓ` with the valuations of `ℓ₀`
  (`v_p(ℓ) = E_p` on `S_b`, `0` elsewhere). `slope_complete` instantiates it with `ℓ₀` through
  `padicValNat_ell`. Valuations above `p` are `vP π hπ` at the prime elements `π ∣ p` of `ℤ[s]`.
  (i) is required at every prime `π ∣ p`, and (ii) asks for `v_π(D_{gj}) ≥ prec j` (`k_j`). The
  conclusion has the three items, `v_p(B) ≥ 4` on `S₀`, and `IsSquare B.den` (the form used by
  `PoleCompleteness`). Item 1 is proved at `p = 2` too, where `v_{(s)} = 2 v_2` on `ℚ`.
- **sb-integrality.** As stated. `M₀ ≥ 1` follows from `M₀ ∣ h`, `h ≠ 0`.
- **selected-prime-precision.** `r` lives in `ZMod p`, as in `GoodPatternPrime`, rather than in
  `ℤ`. The prime `𝔭₁ = (p, s - r)` is a prime element `π` with
  `∀ a, residueAt r hr a = 0 ↔ π ∣ a`. `exists_prime_residueAt` shows such a `π` exists, and then
  `σπ` is `𝔭₂`. The conclusion is `Vge (vP π hπ) (if j < 8 then 1 else 28) (τ_j)` with 0-based
  `j`. The hypotheses `p` odd and `p > 324` are combined as `324 < p`.
- **slope-completeness.** This needs the extra hypothesis `hM0 : 1 ≤ Syntax.M0`: the shift
  choice needs `M₀ ≥ 1`. The size chapter proves it (existence of a successful formal multiple),
  and `ZInQ.Mult.one_le_M0` turns that existence into the hypothesis.
- **completeness.** `multiply_complete` takes, besides `hPC` and `h22`: `hM0`, the fixed-scalar
  semantics of `S_{c_*}` for the constructors `I` (`hS`, the same hypothesis mult-certificate uses
  for the multiply unfolding), and `hI : I.guard T = guardPoly T`. It holds for every `T`.

## Lemmas added beyond the leaves

- PatternValues.lean: valuations of catalogue multipliers (`padicValNat_multiplier_le_small`,
  `padicValNat_multiplier_le_cat`, `not_dvd_multiplier`), `padicValInt_pattern_value`,
  `catalogueSet_prime`, `le_catalogue_sup`.
- PatternSlopes.lean: `pattern_value_spec`, `goodSlope_of_values`, `contactInts`,
  `mem_contactSet_iff`, `GoodSlope.old_le_Cp`.
- PoleLocal.lean: `W⁻¹ ≡ 1` at old primes (`vge_inv_prod_sub_one`), `W⁻¹ ≡ 0 or 1` at a selected
  prime (`vge_inv_prod_selected`), `addVal_prod`.
- PoleValuationsAux.lean: `padicValRat_finset_prod`, `even_padicValRat_contactQuot`,
  `padicValRat_contactQuot_eq_one`, `contact_unique`, `exists_vP_ratCast` (`v_π = e v_p` on `ℚ`,
  `e ∈ {1, 2}`), `vP_star`, `trace_cast_K0`, `exists_prime_dvd_natCast`.
- SquareDen.lean: `isSquare_den_of_even`.
- TestsLocal.lean: `tests_vge_zero_of_W1` (all twelve tests are integral when `H` is formal at `ρ`
  and `V₀` at `σρ`), `vge_invX_of_W1`, `vge_Lam_ratio`, `zOf_eq_zCoord`, `invX_eq_wCoord`.
- SbIntegrality.lean: `Q0_mem_W1` (`[M₀]P₀` is formal above `S_b`), `dvd_Ns_of_mem_S_b`,
  `formalCondition_M0`.
- SelectedReduction.lean: `zsmul_mem_W1_of_pointCount_dvd` (if `#Ẽ_r(𝔽_p) ∣ h` then `[h]P₀` is
  formal at `π`; it uses the existing bridge `card_point_shortCurve` between `Nat.card` of the
  reduced curve and `pointCount`), `res_neg_genD_sq`, `residueAt_neg_ker`.
- SelectedPrecision.lean: `vge_Lam_ratio_sub` (`Λ([nh]P₀)/Λ([h]P₀) ≡ n mod π^28` for `p > 324`),
  `map_truncLog`, `map_Lam`, `mapE_mem_W1`.
- SlopeCompleteness.lean: `exists_prime_residueAt`, `exists_shift`, `padicValRat_ell`.
- Core.lean: `slopes_of_int` (every integer is a sum of three slopes satisfying the slope
  predicate), `exists_common_den`, `completeness_core` (the witnesses of the height certificate
  for `(a, b, ab)`).

## Problems

- `multiply_complete` is not proved yet. Its proof is short once mult-certificate commits
  `HeightCert`/`heightCertificate_rel_iff` and `multiply_rel_iff` (announced shapes:
  `multiply_rel_iff I cs ℓ T hS P Q R : (multiplyTemplate I cs ℓ T).Rel (codes3 P Q R) ↔ ∃ n, P = ι(n 0) ∧ Q = ι(n 1) ∧ R = ι(n 2) ∧ HeightCert ![P, Q, R] ℓ ![cs, cs n₀, cs n₁, cs n₂] ∧ guard`).
  It is `rw [multiply_rel_iff]`, then `n = ![a, b, ab]`, the guard from `guard_true_triple`, and
  `HeightCert` from `completeness_core` (cast the integers `A i k`, `B i` to `ℚ`; the nine sums by
  `fin_cases`).
- Pitfall, reported to mult-certificate and fixed there: a hypothesis `hq : q ∈ S_b` or
  `q ∈ catalogue` used as a term made elaboration evaluate
  `catalogueFinset (4 * primorial 324) 22 324` ("maximum recursion depth"). `catalogue`, `S_b` and
  `S_mul` are now `@[irreducible]`.
- Pitfall: `Dvd.dvd.mul_right` on `Ps * Hcat` caused a kernel deterministic timeout (Mathlib's
  monoid `∣` instance against Nat's). Core `Nat.dvd_trans`/`Nat.dvd_mul_right` avoid it.

## Suggestions for the next agent

- Finish `multiply_complete` as above once `multiply_rel_iff` lands on `wip/mult-certificate`.
- The hypotheses `hM0`, `hS` and `hI` of `multiply_complete` are to be discharged by the size
  chapter (formal multiple), the fixed-scalar semantics (syntax chapter) and the constructor
  instance of the specification.
