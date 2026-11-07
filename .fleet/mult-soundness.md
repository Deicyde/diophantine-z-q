# Report: mult-soundness (blueprint `multiplication/soundness/`)

Modules: `ZInQKernel/Multiplication/Soundness/*.lean`, root `ZInQKernel/Multiplication/Soundness.lean`
(imported from `ZInQKernel.lean`). Namespace `ZInQ.Mult`, following the chapter's shared design.
There is no `sorry` and no `native_decide`. Every leaf theorem depends only on `propext`,
`Classical.choice` and `Quot.sound` (checked with `#print axioms` after a full `lake build ZInQKernel`).
Merged branches: `wip/mult-certificate` (constants, tests, slope predicate, pole obstruction,
the constants' properties, height-certificate semantics, guard, multiply unfolding) and
`wip/mult-formal-log`, whose proof of `ellLog_add` removes the last `sorry` from the soundness chain.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| soundness/height-constant-integers.md | `ZInQ.Mult.height_constants_int` | proved (`decide`) |
| soundness/height-constants.md | `ZInQ.Mult.heightB0`, `heightB0_lt_ten`, `one_lt_log_41_sub` | proved |
| soundness/rational-height-bounds.md | `ZInQ.Mult.rational_height_bounds` (`ratHeight_add3_le`, `ratHeight_div_le`, `ratHeight_neg`, `ratHeight_nonneg`, `ratHeight_inv`) | proved |
| soundness/field-height-bounds.md | `ZInQ.Mult.field_height_bounds` (`hK0_mul_le`, `hK0_add_le`, `hK0_sqrt2`, `hK0_epsilon`, `hK0_epsilon_pow_four_mul_le`, `hK0_ratCast_add_mul_sqrt2_le`) | proved |
| soundness/generator-height.md | `ZInQ.Mult.generator_height` (`canonHeightE`, `canonHeightE_zsmul_genP0`, `log_41_sub_le_two_canonHeightE_genP0`, `two_canonHeight_genP0_gt_one`, `two_canonHeightE_le`, `canonHeightE_zero`) | proved |
| soundness/contact-valuations.md | `ZInQ.Mult.contact_valuations` (general form `contact_valuations_of`) | proved |
| soundness/tests-to-congruence.md | `ZInQ.Mult.tests_to_congruence` (proof on the individual quantities: `tests_to_congruence_aux`) | proved |
| soundness/local-congruence.md | `ZInQ.Mult.local_congruence` (general form `local_congruence_of`) | proved; extra hypothesis `1 ≤ Syntax.M0` |
| soundness/common-group.md | `ZInQ.Mult.common_group` (general form `common_group_of`) | proved |
| soundness/contact-support.md | `ZInQ.Mult.slope_height_le` (general form `slope_height_le_of`) | proved; extra hypothesis `1 ≤ Syntax.M0` |
| soundness/box-inequality.md | `ZInQ.Mult.box_inequality` | proved |
| soundness/finite-box.md | `ZInQ.Mult.finite_box` (also `finite_box_of_heightCert`, `finite_box_of_slopes`, height part `finite_box_of_heights`) | proved; extra hypothesis `1 ≤ Syntax.M0` |
| soundness/soundness.md | `ZInQ.Mult.multiply_sound` | proved; extra hypotheses `1 ≤ Syntax.M0`, `hS`, `hI` (see below) |

## Statement corrections and precisions

- **`M₀ ≥ 1` is a hypothesis.** local-congruence, contact-support, finite-box and soundness take
  `(hM0 : 1 ≤ Syntax.M0)`. Without it `c_* = 0`, `supp(c_*) = ∅`, and the claim `p ∤ c_*` for
  `p ∉ S_mul` is false, so the local congruence would fail. This follows the certificate's
  `not_mem_S_mul`. The size chapter proves the fact (`Size.M0_bounds` on `wip/size-constants`, whose
  formal-multiple existence still has a `sorry` there). Once it lands on main, drop the hypothesis.
- **soundness.** The multiplication template is `multiplyTemplate I c_* ℓ₀ T` for a constructor
  meaning `I`. As in the certificate's `multiply_rel_iff`, two facts about `I` are hypotheses:
  - `hS` is the semantics of the fixed-scalar template `S_{c_*}` (blueprint
    `syntax/fixed-scalar-semantics.md`, not yet formalized).
  - `hI : I.guard T = guardPoly T` identifies the guard polynomial.

  The template's integer arguments are `(Syntax.cstar, Syntax.ell, Syntax.T)`.
- **finite-box.** The 36 parameters of the height-certificate template are described
  coordinatewise: inputs `ι(nᵢ)`, `a₁₅ = ℓ₀`, shift codes `ι(certShifts n i)`. The conclusion is
  `|nᵢ| < T` in `ℤ`.
- **contact-valuations, common-group, local-congruence, contact-support** are stated on the
  certificate's definitions (`slopeR0`, `slopeA`, `slopeR`, `normTests`, `groupW`, `traceTheta`,
  `prec`, `testValues`, `SlopePred`, `certShifts`, `S_b`, `S_mul`). Each has a general form `*_of`
  that takes only the properties of `p` the proof uses:
  - contact-valuations: `p > 61` and `v_p(ℓ) = 0`, `ℓ ≠ 0`;
  - common-group: `p > 324` and `v_p(ℓ) = 0`;
  - local-congruence: also `p ∤ c₀`.
- **contact-valuations.** Only `p > 61` is needed (`|c - c'| ≤ 60`, `|c - 1| ≤ 61`), not `p > 324`.
- **tests-to-congruence.** The tests are the certificate's `testValues h z ![c, cn₁, cn₂, cn₃]`,
  with hypotheses `Vge (vP π hπ) (prec j) (τ j)` at a prime element `π ∣ p` of `ℤ[s]`. The case
  `Uᵢ = O` (the ratio is `0`) is handled inside `ratioAt_eq`, through `z = 0`.
- **common-group.** The conclusion is `∃ g, ∃ π prime, π ∣ p, ∀ j, k_j ≤ v_π(D_{gj})`. The
  argument picks the pair `(g, 𝔮)` by contradiction: if every `2 v_𝔮(W_g⁻¹) ≥ r`, then
  `v_p(Θ) ≥ (r+1)/2`, and the pole input would have negative odd valuation.
- **rational-height-bounds.** `ratHeight_div_le` and `ratHeight_inv` hold without `y ≠ 0`
  (`x/0 = 0`). The bundled statement keeps the article's hypothesis.
- **generator-height.** `ĥ` on `E(K₀)` is `canonHeightE Q = canonHeight (theta Q)`. Item (3) is
  stated for `Q = Point.some x y h`.

## Lemmas added beyond the leaves

- `RationalHeights`: `ratHeight_eq_logHeight₁`, which identifies `ratHeight` with Mathlib's `logHeight₁`
  on `ℚ`, plus `totalWeight_rat` and `ratHeight_mul_le`.
- `FieldHeights`: `totalWeight_K0`, `hK0_pow`, `hK0_ratCast_eq_ratHeight`.
- `HeightConstants`: `one_add_sqrt_two_pow_twelve`, `one_add_sqrt_two_pow_twelve_lt`.
- `ContactValuations`: `exists_int_of_mem_contactSet`, `padicValRat_intCast_eq_zero`,
  `padicValRat_add_eq_zero`, `padicValRat_prod_eq_zero`, `lt_of_not_mem_S_b`,
  `padicValRat_ell_of_not_mem`, `ell_cast_ne_zero`.
- `CommonGroup`: `exists_prime_dvd_natCast` (a prime of `ℤ[s]` above `p`), `star_dvd_natCast`,
  `vp_prod`, `vp_one'`, `vp_one_add_mul_sq`.
- `TestsToCongruence`:
  - `logAt`, `ratioAt`, `rhoAt` are the test quantities at `[m]P₀`, defined through the
    certificate's `Lam` and `invX`;
  - `map_truncLog`, `vP_star` (additive form of `vp_star`), `mapE_ne_zero`;
  - `mapE_mem_W1` (`v_π(ρ) ≥ 1` puts the point in `E₁(K_π)`), `algebraMap_logAt`;
  - `ratioAt_eq`: `Λ([u]P₀)/Λ([h]P₀) = (u/h)(1 + δ)` with `v_π(δ) ≥ 28`;
  - `integral_of_rel`, `rel_close`, `vP_intCast_eq_zero`.
- `ContactSupport`: `contactSupport_pow_dvd`, `pow_24_le_rpow`.
- `FiniteBox`: `heightB0_nonneg`, `two_sq_canonHeightE_le`, `nineQ_surj`.

## Problems

- `ZInQ.Mult.pole_obstruction` and `abscissa_val_even` come from the certificate branch. I first
  wrote my own copies, then deleted them after merging, so there is no duplicate.
- Instance-path mismatch between `genCurve.toAffine.Point` and `(shortCurve _).toAffine.Point`:
  - `wCoord_some`, `zCoord_some` and `zero_smul` do not rewrite on `genCurve` points.
  - The workarounds were `generalize` plus `rcases` on the point, `show` with the definitional
    unfolding, and `zero_zsmul`.

## Suggestions for the next agent

- When the size chapter's `M0_bounds` is on main, remove `hM0` from `local_congruence`,
  `slope_height_le`, `finite_box*` and `multiply_sound`.
- When `syntax/fixed-scalar-semantics` is formalized for the library's constructors, discharge `hS`
  and `hI` in `multiply_sound`. Then combine it with completeness for input M.
