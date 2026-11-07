# Blueprint audit: multiplication, assembly and main (task bp-audit-mult)

Scope: the 80 articles under `blueprint/roadmap/multiplication/` (50), `blueprint/roadmap/assembly/`
(23) and `blueprint/roadmap/main/` (7) whose frontmatter has `statement: formalized`, at commit
`de90139`. For each article I compared the statement (the text before **Proof sketch.**) with the
Lean declarations named in its `lean:` field: hypotheses, quantifiers and ranges, conclusions,
constants, and the objects the statement is about.

## Summary

- **No Lean statement is weaker than its article in a way that matters for a consumer.** No
  `lean:` name is wrong: all 183 recorded names exist (`#check` in a scratch file against the
  built tree).
- **Three statements drifted slightly**. I edited each article to say what the Lean proves:
  - `multiplication/local/chord-estimate.md`: the tangent case;
  - `multiplication/local/dyadic-generator.md`: completion versus `K₀`;
  - `multiplication/completeness/pattern-slopes.md`: "the unique `c`".
- **One extra Lean hypothesis.** It is the expected one: `assembly/assembly-lemma.md` (`Pstar_spec`,
  `assembly`) takes `HaltingNodeCheck`. I added one sentence to the article saying that the proof
  uses this finite computation. I found no other extra hypothesis.
- **Lean stronger than the article** in 13 articles, as follows:
  - weaker hypotheses: M instead of H, PC, 22P; no Mordell–Weil; no disjointness; any sign of
    `η`; `p` not required odd;
  - a general valuation where the article has a discrete one;
  - parametric constructor records.
- **Two tooling notes were removed from article prose** ("The Lean lemma behind …",
  "For a Lean proof …"). Article text must not mention Lean.
- **Many `lean:` lists are incomplete.** The claims are proved, under names the field does not
  record. They are listed in the table and collected under "Missing names" below. I did not edit
  any frontmatter.
- The main/ articles and `assembly/approximation/real-derivative.md`, `real-subtraction.md` were
  audited in `lean-audit-2026-11-06.md`. Since then their statements are unchanged: only the
  `lean:` field of `main-theorem.md` and the dependency list of `real-derivative.md` changed, and
  the Lean changes are cosmetic. `assembly-lemma.md`, `ordinary-value-relation.md`,
  `multiplication-template.md` and `main-theorem.md` were also covered by
  `final-audit-2026-11-07.md`; their texts are unchanged since then (apart from my one sentence in
  `assembly-lemma.md`).

Checks run:
- `lake build ZInQKernel` succeeds; the only `sorry` warning is `Main.lean:34`, the expected
  four-hypothesis theorem.
- `#check` of all 183 recorded names and of the 41 proposed additional names: all exist.
- `uv run --project ~/autoform-dzq autoform check blueprint --lean-root .` passes after the edits
  (353 articles, 1201 dependencies).

## Verdicts

Lean names are in namespace `ZInQ.Mult` (multiplication), `ZInQ.Assembly` (assembly) or `ZInQ`
(main) unless written in full.

### multiplication/

| Article | Lean names | Verdict | Change / remark |
| --- | --- | --- | --- |
| abscissa-parity.md | abscissa_val_even | faithful | — |
| pole-obstruction.md | pole_obstruction | faithful | — |
| multiplication-template.md | multiplication_exact, multiplication_exact_unique, multiplication_existsUnique | faithful (final audit; unchanged) | — |
| certificate/clearing-arithmetic.md | clearing_arithmetic, clearing_identities | faithful | `clearing_arithmetic` uses ℕ subtraction; `clearing_identities` shows that nothing truncates |
| certificate/constants.md | S_ht, catalogue, S_b, S_mul, Bp, Cp, Dp, Ep, contactPoly, IsOddContactPrime, prec | faithful (definitions) | 𝒞 and `M_S` are `ZInQ.contactSet`, `ZInQ.contactSupport` (unlisted); the fixed constants are `ZInQ.Syntax.M0`, `cstar`, `ell`, `R`, `Aht`, `T` |
| certificate/constants-properties.md | one_le_M0, one_le_M0_spec, four_le_cstar, one_le_ell, S_mul_admissible, Aht_eq_heightH6, sixContact_at_Smul, four_lt_T, prime_of_mem_catalogue, catalogue_injective, Hcat_squarefree, padicValNat_ell, not_mem_S_mul | faithful | item 3 (`A_ht ≥ 2·10¹³`, `48A_ht ≥ 1`) is `ZInQ.Syntax.two_mul_ten_pow_thirteen_le_Aht` and `one_le_forty_eight_mul_Aht` (unlisted). `one_le_M0` is a conditional form; `one_le_M0_spec` is item 1 |
| certificate/guard-true-triples.md | guard_true_triple, guard_false_triple, guard_rel_iff, guardPoly_zero_set | faithful (Lean parametric) | stated for any constructor record with `guard T = guardPoly T` and any `T`; `specConstructors` satisfies this by `rfl` |
| certificate/height-certificate-semantics.md | heightCertificate_rel_iff, HeightCert | faithful | — |
| certificate/local-templates.md | rawZ_rel_iff_of, rawZ_not_rel, rawInverseX_rel_iff_of, rawInverseX_not_rel, log25_rel_iff, rawZ_rel_iota, rawInverseX_rel_iota | faithful; Lean stronger | the `ι(n)` forms need no generator-certificate assumption |
| certificate/multiply-unfolding.md | multiply_rel_iff_unguarded, multiply_rel_iff, multiply_rel_iff_cert | faithful (Lean parametric) | all three take the scalar-template semantics `hS` as a hypothesis; for `specConstructors` it is `spec_scalar_cstar_rel_iff` (unlisted), which consumers use |
| certificate/slope-predicate.md | SlopePred, slopeR0, slopeA, slopeR, normTests, groupW, traceTheta, certShifts | faithful (definition) | — |
| certificate/slope-semantics.md | slope_rel_iff | faithful | — |
| certificate/test-group-semantics.md | testGroup_rel_iff, testGroup_rel_iff_codes | faithful | — |
| certificate/twelve-tests.md | invX, zOf, Lam, testValues, testValues_eq | faithful (definition) | — |
| completeness/completeness.md | multiply_complete | faithful | — |
| completeness/pattern-slopes.md | pattern_slopes, GoodSlope | slight drift, fixed | Lean: `v_p(t−c) = 1` for **every** `c ∈ 𝒞` with `v_p(t−c) > 0`. The article said "for the unique `c`". Now: "for every `c` … (only one such `c`, because `p > 324` divides no difference of two elements of 𝒞)". The "in particular ≤ C_p" is `GoodSlope.old_le_Cp` (unlisted) |
| completeness/pole-input-positivity.md | pole_input_small | faithful | — |
| completeness/pole-input-valuations.md | pole_input_valuations, poleInput | faithful; Lean stronger | any `ℓ ≠ 0` with `v_p(ℓ) = E_p` on `S_b` and `0` elsewhere; `ℓ₀` qualifies by `padicValNat_ell` |
| completeness/sb-integrality.md | tests_integral_old | faithful | — |
| completeness/selected-prime-precision.md | tests_precision_selected | faithful | `𝔭₁` is given by a prime element `π` with `π ∣ a ⟺ a ↦ a₀ + a₁r ≡ 0` |
| completeness/shift-choice.md | shift_choice, shift_choice' | faithful | — |
| completeness/slope-completeness.md | slope_complete | faithful | — |
| completeness/weak-approximation.md | weak_approx_q | faithful; Lean stronger | no disjointness of `S`, `S'`; also gives `q ≠ 0` |
| local/chord-estimate.md | chord_add_five, formal_third_point_five | slight drift, fixed | For `P₁ = P₂` the article said the line is the tangent. Lean gives a line through the point with the bounds and the identity, without identifying it as the tangent. Hypotheses: only `y ≠ 0`, `v(x/y) ≥ k`, `v(1/y) ≥ 3k` (implied by `W_k`), `P₁+P₂ ≠ O`, any additive valuation. Statement now: "there is a line through `P₁` and `P₂` …; for `P₁ ≠ P₂` it is the line through the two points (injectivity of `z`)". Conclusion `v(ω(P₁+P₂)) ≥ 3k` added. The tooling sentence in the sketch was replaced by the tangent-case remark |
| local/dyadic-generator.md | genP0_val_s, genP0_mem_formalFilt_three | slight drift, fixed | Lean states `P₀ ∈ E₃` over `K₀` at `v_s`; the article said "in the completion `K_(s)`". Now stated over `K₀`, with a remark that the completion gives the same. The multiples clause is `zsmul_genP0_mem_formal` (unlisted) |
| local/formal-group-law.md | omegaSeries_hasSum, formalAdd, formalGroupLaw_exists, hasSum_formalAdd | faithful; Lean stronger (`A` may be `0`) | part 1 (functional equation, uniqueness, form `T³(1+⋯)`, integrality) is `omegaSeries_eq`, `omegaSeries_unique`, `omegaSeries_lowCoeffs`, `omegaSeries_integral` (unlisted) |
| local/formal-group.md | formal_val_x_y, formalFilt, mem_formalNbhd_iff, zCoord_injOn, zsmul_mem_formalFilt | faithful; Lean stronger | any additive valuation `K → ℤ ∪ {∞}`, no characteristic or normalization assumption, `A` may be `0`. Part 4 verbatim is `zsmul_mem_W1`; part 2 also uses `mem_formalFilt_iff`, `add_mem_filt` (unlisted). Tooling parenthetical in the sketch reworded |
| local/formal-logarithm.md | formalLog, ellLog, formalLog_formalAdd, ellLog_add, summable_log | faithful | `log` is defined as `Σ binom(2j,j) Aʲ T^{4j+1}/(4j+1)`. `d log/dT` = invariant differential, `b₀ = 1`, `bᵢ ∈ 𝒪` and `λ([n]P) = nλ(P)` are `derivative_formalLog`, `invDiffCoeff_spec`, `ellLog_zsmul` (unlisted); the link to `dx/(2y)` is in logarithm-series |
| local/generator-dyadic-numerals.md | genP0_dyadic_numerals | faithful | — |
| local/logarithm-coefficients.md | log25_coefficients, truncLog_eq | faithful | the factorization, `d² = 11243 − 7950s` and the "Consequently" are `sixteen575_factor`, `ZInQ.genD_sq`, `truncLog_eq_trunc` (unlisted) |
| local/logarithm-isometry.md | evalLog_isometry, ellLog_injOn, val_z_zsmul_eq | faithful | `v(λ(P)) = v(z(P))` and the "in particular" (`p` odd, `e = 1`: injective, torsion-free) are `ellLog_val_eq`, `ellLog_unramified` (unlisted) |
| local/logarithm-nonvanishing.md | log25_z_ne_zero | faithful | — |
| local/logarithm-ratio.md | ellLog_ratio | faithful; Lean stronger | no Mordell–Weil hypothesis (the article assumes it; it is now proved anyway) |
| local/logarithm-series.md | uSeries_eq, invDiffSeries_ode, coeff_formalLog_genE | faithful | stated for general `A` in characteristic 0. Part 1 is also `uSeries_unique`, `one_sub_uSeries_sq`, `X_mul_uSeries`, `uSeries_genE_unit`; part 2 is `invDiffSeries_sq`, `invDiffSeries_mul`, `X_mul_derivative_uSeries` (all unlisted). `invDiffSeries_ode` is auxiliary |
| local/primes-above-p.md | primeR_split, primeP_inert, vp_ratCast, vp_star, vp_trace_ge | faithful | prime elements stand for prime ideals (PID). `v_π(0) = 0` is a junk value, harmless (part 4 has the disjunct `Tr y = 0`). The residue isomorphism is `quotPrimeREquiv`, `quotPrimeREquiv_mk` (unlisted) |
| local/truncation-error.md | log25_truncation_error | faithful | the `P = O` remark is `log25_truncation_zero` (unlisted) |
| local/truncation-unit.md | truncLog_eq_mul_unit, log25_eq_mul_unit, log25_ne_zero | faithful | the completion case is the generic `truncLog_eq_mul_unit` (needs `v(16575) ≤ 2`, `v(d²) ≥ 0`) |
| soundness/box-inequality.md | box_inequality | faithful | — |
| soundness/common-group.md | common_group | faithful | — |
| soundness/contact-support.md | slope_height_le | faithful | — |
| soundness/contact-valuations.md | contact_valuations | faithful | — |
| soundness/field-height-bounds.md | field_height_bounds | faithful | — |
| soundness/finite-box.md | finite_box | faithful | — |
| soundness/generator-height.md | generator_height, canonHeightE | faithful | — |
| soundness/height-constant-integers.md | height_constants_int | faithful | — |
| soundness/height-constants.md | heightB0, heightB0_lt_ten, one_lt_log_41_sub | faithful | — |
| soundness/local-congruence.md | local_congruence | faithful | — |
| soundness/rational-height-bounds.md | rational_height_bounds | faithful | — |
| soundness/soundness.md | multiply_sound | faithful | — |
| soundness/tests-to-congruence.md | tests_to_congruence | faithful | — |

### assembly/

| Article | Lean names | Verdict | Change / remark |
| --- | --- | --- | --- |
| approximation/close-completeness.md | close_complete | faithful; Lean stronger | hypothesis is M (`MultiplicationExact` for the specified template) instead of H, PC, 22P; M follows from these by `Mult.multiplication_exact` |
| approximation/close-relation.md | close_relation_iff | faithful; Lean stronger | under M, as above |
| approximation/close-soundness.md | close_sound | faithful; Lean stronger | under M, as above |
| approximation/real-accumulation.md | exists_multiple_large_unconditional | faithful | — |
| approximation/real-derivative.md | zCoord, z_ratio_tendsto | faithful (lean-audit; statement unchanged) | — |
| approximation/real-subtraction.md | realCurve, RealCurve.TendstoPt, RealCurve.exists_subseq_tendstoPt, RealCurve.tendstoPt_sub_zero | faithful (lean-audit; unchanged) | — |
| assembly-lemma.md | Pstar_spec, assembly | extra hypothesis `HaltingNodeCheck` (expected) | added: "Besides the four hypotheses, the proof uses one finite computation: the node statistics of the universal halting circuit, on which the witness accounting and the size bounds of B depend." Otherwise faithful (final audit F2) |
| local-tests/deep-multiples.md | exists_smul_mem_Ek, exists_common_smul_mem_Ek | faithful | — |
| local-tests/dyadic-trace.md | vS_star, vS_trace_ge | faithful | `Tr x = 0` disjunct for the junk `v(0) = 0` |
| local-tests/formal-multiplication.md | val_zCoord_add_sub, val_zCoord_zsmul_sub, zsmul_mem_formalFilt_succ, zsmul_mem_formalFilt_add_val, zCoord_zsmul_eq_mul_unit | faithful; Lean stronger | no characteristic assumption; item 4 does not need `p` odd. Item 3 is stated with `k + e·v_p(n)`, which equals `k + v(n)` under the residue-characteristic assumption by `val_intCast_eq` (unlisted) |
| local-tests/pole-input-local.md | poleInput_local | faithful; Lean stronger | `η` is any sign with `η² = 1`; the article requires the sign of `F(n)` |
| local-tests/pole-input-real.md | poleInput_real | faithful | — |
| local-tests/test-completeness.md | test_complete | faithful | — |
| local-tests/test-divisibility.md | test_dvd | faithful | — |
| main-branch-exactness.md | main_branch_eq | faithful | — |
| ordinary-value-relation.md | value_relation_iff, exists_value_relation_iff | faithful (final audit; unchanged) | — |
| value-templates/close-coordinates-semantics.md | closeCoordinates_rel_iff | faithful | — |
| value-templates/double-and-add-chains.md | chain_value, chain_satisfiable, chainBuild_binDigits_value, chainCount_contacts | faithful | the count "one bits + bit length − 1" is `chainBuild_length` with the definition of `chainCount`; also `binVal_binDigits` (unlisted) |
| value-templates/exceptions-semantics.md | exceptions_rel_iff | faithful | — |
| value-templates/outer-recipe-relations.md | close_rel_iff, main_rel_iff, valueUnion_rel_iff, value_rel_iff, spec_close_rel_iff, spec_main_rel_iff, spec_valueUnion_rel_iff, spec_value_rel_iff | faithful | the generic forms take well-formedness and witness-count hypotheses on the called entries; the `spec_*` forms are for the specified library |
| value-templates/signed-encoding-semantics.md | signedEncode_rel_iff | faithful; Lean stronger | under M; the "equivalently" uses `ZInQ.Compiler.Precision.dec_enc`, `enc_dec` (unlisted) |
| value-templates/six-local-tests.md | Test, test_iff | faithful (definition) | — |
| value-templates/value-test-semantics.md | valueTest_rel_iff | faithful; Lean stronger | under M |

### main/

| Article | Lean names | Verdict | Change / remark |
| --- | --- | --- | --- |
| catalogue-bound.md | CatalogueBound | faithful (lean-audit; unchanged) | — |
| frozen-target.md | FrozenTarget | faithful (lean-audit; unchanged) | — |
| main-theorem.md | exists_bounded_integer_polynomial_defining_integers_of, exists_bounded_integer_polynomial_defining_integers_of_nodeCheck | faithful (statement only) | the first name states the article exactly and is the expected `sorry`. The second is the proved form, with the expected extra hypothesis `HaltingNodeCheck`. The article has no `proof:` field, which is correct |
| mordell-weil.md | MordellWeilE | faithful (lean-audit; unchanged) | — |
| pole-completeness.md | PoleCompleteness | faithful (lean-audit; unchanged) | — |
| prime-pattern.md | FixedPrimePattern | faithful (lean-audit; unchanged) | — |
| six-contact-estimate.md | SixContactEstimate | faithful (lean-audit; unchanged) | — |

## Missing names (proposed additions to `lean:`; all exist and state the article's claim)

- **multiplication/local:**
  - dyadic-generator: `ZInQ.Mult.zsmul_genP0_mem_formal`.
  - formal-group-law: `omegaSeries_eq`, `omegaSeries_unique`, `omegaSeries_lowCoeffs`, `omegaSeries_integral`.
  - formal-group: `zsmul_mem_W1`, `mem_formalFilt_iff`, `add_mem_filt`.
  - formal-logarithm: `derivative_formalLog`, `invDiffCoeff_spec`, `ellLog_zsmul`.
  - logarithm-coefficients: `sixteen575_factor`, `truncLog_eq_trunc`, `ZInQ.genD_sq`.
  - logarithm-isometry: `ellLog_val_eq`, `ellLog_unramified`.
  - logarithm-series:
    - part 1: `uSeries_unique`, `one_sub_uSeries_sq`, `X_mul_uSeries`, `uSeries_genE_unit`;
    - part 2: `invDiffSeries_sq`, `invDiffSeries_mul`, `X_mul_derivative_uSeries`.
  - primes-above-p: `quotPrimeREquiv`, `quotPrimeREquiv_mk`.
  - truncation-error: `log25_truncation_zero`.
- **multiplication/certificate:**
  - constants: `ZInQ.contactSet`, `ZInQ.contactSupport`, `mem_S_ht`, `contactPoly_eq_prod`.
  - constants-properties: `ZInQ.Syntax.two_mul_ten_pow_thirteen_le_Aht`, `one_le_forty_eight_mul_Aht`,
    `padicValNat_ell_of_mem`, `padicValNat_ell_of_not_mem`.
  - multiply-unfolding: `spec_scalar_cstar_rel_iff`.
- **multiplication/completeness:** pattern-slopes: `GoodSlope.old_le_Cp`.
- **assembly:**
  - formal-multiplication: `val_intCast_eq`.
  - double-and-add-chains: `chainBuild_length`, `binVal_binDigits`.
  - signed-encoding-semantics: `ZInQ.Compiler.Precision.dec_enc`, `enc_dec`.

## Consumers

No consumer article needs more than the Lean of its dependency provides:
- The chord estimate is used in formal-multiplication only through the existence of the line and
  the `5k` bound.
- The dyadic position of `P₀` is used, in deep-multiples, logarithm-nonvanishing and the
  formal-multiple articles, through valuations on `K₀`.
- The Lean proofs of all these consumers are complete.

## Method

- I read every article statement in full and compared it with the source statements, together
  with the section variables (valuation type, `include`d hypotheses).
- For the declarations with section variables I also read the elaborated `#check` output:
  `chord_add_five`, `formal_val_x_y`, `common_group`, `tests_to_congruence`, the
  formal-multiplication lemmas and `truncLog_eq_mul_unit`.
- I checked the definitions behind each statement: `GoodSlope`, `GoodPatternPrime`,
  `pointCount`, `SlopePred`, `HeightCert`, `Test`, `poleInput`, `chainCount`, `specConstructors`,
  `formalFilt`, `ResidueChar`, `logCoeffA`, `vK`.
- Lean ran one process at a time.
