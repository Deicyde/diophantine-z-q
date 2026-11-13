# Lean audit of the formalized blueprint articles (task lean-audit)

Scope: the 67 articles under `blueprint/roadmap/` whose frontmatter has `statement: formalized`
(`grep -rl '^statement: formalized' blueprint/roadmap`), at commit `0bea4dc`.

## Summary

- **No Lean statement is false, vacuous or weaker than its article.** All four hypotheses (H, PC,
  22P, CAT), `MordellWeilE` and `FrozenTarget` say exactly what the manuscript says.
- **Two records overclaim** (verdict WRONG): each article contains a sentence that no Lean
  declaration states, yet the frontmatter records `proof: formalized`.
  - `model/descent/torsion.md`: "P₀ has infinite order". The fact is missing, and downstream
    files carry it as a hypothesis. A three-line proof compiles; see below.
  - `syntax/language/absolute-value-gadget.md`: the template consequence
    "Rel_value.abs(x,a) ⟺ a = |x|".
- **Many `lean:` lists are incomplete.** The claims are proved, but under names that were never
  recorded. These are listed under lesser remarks.

Checks run:
- `lake build ZInQKernel` succeeds.
- `python3 scripts/check_target.py` prints `FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean`.
- All 137 names recorded in `lean:` fields exist. `#print axioms` on each gives only `propext`,
  `Classical.choice` and `Quot.sound` (`ZInQ.Zs` uses none). The one exception is
  `exists_bounded_integer_polynomial_defining_integers_of`, which also has `sorryAx` from
  Main.lean's single `sorry`. Its article records no proof, so this is expected.
- In `ZInQKernel/`, outside the Main.lean `sorry`, there is no `sorry`, `admit`, `native_decide`,
  `implemented_by`, `extern`, `axiom`, `unsafe`, `opaque`, `set_option` (none at all, so no
  option that skips kernel checking), `#eval` or `run_cmd`. The kernel search uses `decide +kernel`.

## Verdicts

| Article | Lean names | Verdict |
| --- | --- | --- |
| main/frozen-target.md | FrozenTarget | faithful |
| main/main-theorem.md | exists_bounded_integer_polynomial_defining_integers_of | faithful (statement only; proof is the expected `sorry`) |
| main/six-contact-estimate.md | SixContactEstimate | faithful (real `R`, harmless, see remarks) |
| main/pole-completeness.md | PoleCompleteness | faithful |
| main/mordell-weil.md | MordellWeilE | faithful |
| main/prime-pattern.md | FixedPrimePattern | faithful |
| main/catalogue-bound.md | CatalogueBound | faithful |
| model/point-codes.md | pointCode, iota | harmless difference ("distinct indices have distinct codes" exists only conditionally, see torsion) |
| model/field/quadratic-field.md | K0, sqrt2, epsilon, delta, Zs | harmless difference (list incomplete) |
| model/field/integers-pid.md | Zs.isPrincipalIdealRing, Zs.uniqueFactorizationMonoid | harmless difference (list incomplete) |
| model/field/special-primes.md | prime_sqrt2Z, prime_genDZ, vS_formula_withTop | harmless difference (list incomplete) |
| model/field/units.md | Zs_unit_sqClass, isSquare_of_totallyPositive_unit | harmless difference (list incomplete) |
| model/field/dyadic-valuation.md | vS_sq_add_one, val_s_sq_add_delta_sq | faithful |
| model/field/residue-checks.md | residues_mod_seven, not_isSquare_neg_one_zmod_seven | faithful |
| model/field/generator-curve.md | genCurve, genCurve_two_torsion | faithful |
| model/field/generator-point.md | genP0 | faithful |
| model/field/generator-point-equation.md | genP0_equation | harmless difference (`y₀ ≠ 0` is the unlisted `genY0_ne_zero`) |
| model/field/point-code-properties.md | pointCode_injective, iota_add | harmless difference (list incomplete) |
| model/field/division-polynomial-multiples.md | mulByN_formulas | faithful |
| model/descent/kummer-map.md | Descent.SqClass, sqc, kummer, phi, rescale | faithful |
| model/descent/kummer-homomorphism.md | Descent.kummer_add, Descent.kummerHom | faithful |
| model/descent/kummer-kernel.md | Descent.kummer_eq_one_iff | faithful |
| model/descent/isogeny-doubling.md | Descent.rescale_phi_phi, phiHatE_phiE | faithful (`IsElliptic` instances replace "char ≠ 2, b ≠ 0") |
| model/descent/coordinate-change.md | curveC, theta, theta_some, curveC_two_torsion, two_nsmul_theta_eq_zero_iff, kummer_theta | faithful (list incomplete) |
| model/descent/first-descent-image.md | kummer_range_E, card_kummer_range_E, descentGroup_eq | faithful |
| model/descent/second-descent-image.md | kummer_E'_trivial | faithful |
| model/descent/descent-index.md | index_two_E, index_two_genCurve, kummer_range_eq_descentGroup, two_smul_range_eq_ker | harmless difference (E/2E ≅ ⟨−1,ε,d⟩ is not built as an isomorphism; it follows from the listed facts) |
| model/descent/reduction-point-counts.md | pointCounts_17_23 | faithful |
| model/descent/reduction-torsion.md | red_add, eq_zero_of_red_eq_zero | faithful (more general) |
| model/descent/torsion.md | mem_torsion_E_iff, card_torsion_E | **WRONG** (claim "P₀ has infinite order" not formalized) |
| model/descent/point-r-certificate.md | pointR, theta_symm_two_smul_pointR | harmless difference (items 1–2 proved under unlisted names) |
| model/descent/odd-free-index.md | odd_free_index | faithful (stronger: any `S`) |
| model/descent/mordell-weil-from-descent.md | mordellWeilE | faithful (`example : MordellWeilE := mordellWeilE` checks) |
| model/descent/rank-one.md | exists_generator_E, exists_generator_C | harmless difference (E generator not tied to θ⁻¹(S) in the statement) |
| model/heights/x-height.md | hK0, hx | faithful |
| model/heights/x-height-formula.md | hK0_div, hK0_div_of_isCoprime, hK0_ratCast | faithful |
| model/heights/height-comparisons.md | height_comparisons | faithful |
| model/heights/canonical-height.md | canonHeight | faithful (limUnder junk value excluded by `canonHeight_tendsto`) |
| model/heights/canonical-height-quadratic.md | canonHeight_parallelogram, canonHeight_zsmul | faithful |
| model/heights/canonical-height-bounds.md | canonHeight_tendsto, two_canonHeight_le, hx_le_two_canonHeight, canonHeight_two_smul, canonHeight_add_twoTorsion | harmless difference (ĥ(−T)=ĥ(T), ĥ ≥ 0 unlisted) |
| model/heights/duplication-forms.md | F2, G2, x_two_smul_C | harmless difference (y = 0 clause unlisted) |
| model/heights/duplication-archimedean.md | duplication_archimedean | harmless difference (σ± sentence unlisted) |
| model/heights/duplication-common-divisor.md | duplication_common_divisor | faithful (stronger: gcd-maximality hypothesis unused) |
| model/heights/duplication-height-bounds.md | hx_two_smul_bounds | faithful |
| model/heights/height-of-2r.md | hx_two_R | faithful |
| model/heights/r-torsion-translates.md | x_pointR_add_cT0, x_pointR_add_cTdelta, x_pointR_add_cTnegdelta | faithful |
| model/heights/search-box.md | search_box | faithful (stronger in the rational case) |
| model/heights/square-test.md | SqTest, isSquare_iff_sqTest | faithful |
| model/heights/small-height-bound.md | canonHeight_R_pos, hx_lt_log_nine_of_multiple | faithful |
| model/heights/small-height-search.md | smallHeight_search | faithful |
| syntax/division-polynomials.md | normDiv, divPsi, psiComponent | harmless difference (the "constructor psi" sentence is only parametric, see template-semantics) |
| syntax/division-polynomials-classical.md | normDiv_eq_preΨ', divPsi_eq_Ψ, mk_divPsi, psiEval_eq_evalEval_ψ | faithful |
| syntax/division-polynomial-multiplication.md | DivisionPolynomialMultiplication | faithful |
| syntax/field-pair-arithmetic.md | Pair.val, holds_feq, holds_curve | harmless difference (list covers only part 2; `holds_curve` is not a claim of this article) |
| syntax/nonzero-gadgets.md | exists_mul_eq_one_iff, exists_mul_pairNorm_eq_one_iff | faithful (list incomplete) |
| syntax/sum-of-squares-semantics.md | Formula.ev_compile_eq_zero_iff, ev_sum_sq_eq_zero_iff, ev_prod_eq_zero_iff | faithful |
| syntax/template-semantics.md | Template.denote, Recipe.denote, ExPoly.Rel | harmless difference (documented: `fixed`/`psi`/`guard` read through an abstract `Constructors` record) |
| syntax/language/call-semantics.md | ev_callPoly, ExPoly.exists_blockUpdate_call_iff | faithful (the displayed formula verbatim is the unlisted `ExPoly.ev_call`) |
| syntax/language/existential-lifting.md | Formula.exists_blocks_iff | faithful |
| syntax/language/field-pair-gadgets.md | Pair, Build.fdiv, Build.zGadget | faithful (list incomplete) |
| syntax/language/point-references.md | pointRef, generatorConstraints | faithful |
| syntax/language/generator-references.md | pointRef_eval_generator, generatorConstraints_eq_zero_iff | harmless difference (stated with `codeP0`/`codeNegP0`, not `iota 1`/`iota (-1)`; equal, checked) |
| syntax/language/rational-constants.md | ev_globals_eq_zero_iff, generator_values | faithful (assumes `q ≠ 0`, more general than `q ≥ 2`) |
| syntax/language/positivity-gadget.md | pos_iff_four_squares, exists_blockUpdate_posFormula_iff | faithful |
| syntax/language/absolute-value-gadget.md | eq_abs_iff_four_squares | **WRONG** (template consequence not formalized) |
| assembly/approximation/real-derivative.md | Assembly.zCoord, Assembly.z_ratio_tendsto | faithful (for every `τ : K0 →+* ℝ`) |
| assembly/approximation/real-subtraction.md | Assembly.realCurve, RealCurve.TendstoPt, RealCurve.exists_subseq_tendstoPt, RealCurve.tendstoPt_sub_zero | faithful |

Lean names are in namespace `ZInQ` (the `Syntax.` ones in `ZInQ.Syntax`, the `Assembly.` ones in
`ZInQ.Assembly`).

## WRONG items

### 1. model/descent/torsion.md: "P₀ has infinite order" is not formalized

- **Recorded names.**
  - `ZInQ.mem_torsion_E_iff` (Model/Descent/Torsion.lean:110) says the torsion of `E(K₀)` is
    `{O, (0,0), (d,0), (−d,0)}`.
  - `ZInQ.card_torsion_E` (Model/Descent/RankOne.lean:98) says this torsion has order 4.
  - Both are correct.
- **What is missing.** The article also says "In particular P₀ has infinite order", with
  `proof: formalized`. No declaration states this: `grep -rn 'IsOfFinAddOrder genP0' ZInQKernel`
  finds it only as a hypothesis, documented there as "not yet formalized":
  - `ZInQ.iota_eq_psi (hP0 : ¬ IsOfFinAddOrder genP0)` (Model/DivisionPolynomials/FixedPointCodes.lean:51)
  - `ZInQ.Assembly.exists_multiple_large (hP0 : ¬ IsOfFinAddOrder genP0)` (Assembly/Real/Accumulation.lean:148)
  - `ZInQ.iota_injective_of_addOrderOf_eq_zero (h : addOrderOf genP0 = 0)` (Model/Field/Codes.lean:109),
    which is the "distinct indices have distinct codes" sentence of model/point-codes.md.

  The record therefore claims a fact that later files still treat as an assumption.
- **Fix.** Add the theorem below to Model/Descent/Torsion.lean, after `mem_torsion_E_iff`, and
  add `ZInQ.not_isOfFinAddOrder_genP0` to the article's `lean:` list. It compiled in a scratch
  file against the current tree:
  ```lean
  theorem not_isOfFinAddOrder_genP0 : ¬ IsOfFinAddOrder genP0 := by
    intro h
    rcases (genCurve_two_torsion genP0).mp ((isOfFinAddOrder_iff_two_nsmul_eq_zero genP0).mp h)
      with h | h | h | h
    · exact genP0_ne_zero h
    all_goals
      simp only [genP0, genT0, genTd, genTnegd, Point.mk, Point.some.injEq] at h
      exact genY0_ne_zero h.2

  example : addOrderOf genP0 = 0 := addOrderOf_eq_zero_iff.mpr not_isOfFinAddOrder_genP0
  ```
  The three hypotheses above can then be discharged. The C version (`mem_torsion_C_iff`,
  `card_torsion_C`), which the article also states, exists and should be listed as well.

### 2. syntax/language/absolute-value-gadget.md: the template consequence is not formalized

- **Recorded name.** `ZInQ.Syntax.eq_abs_iff_four_squares (a x : ℚ) : a = |x| ↔ ∃ z : Fin 4 → ℚ,
  a = z 0^2 + z 1^2 + z 2^2 + z 3^2 ∧ a^2 = x^2` (Syntax/Language/Gadgets.lean:93). It is exactly
  the first displayed equivalence, and it is correct.
- **What is missing.** The article goes on: "Consequently, for the absolute-value template,
  Rel_value.abs(x,a) ⟺ a = |x| for all x, a ∈ ℚ", with `proof: formalized`. No `value.abs`
  template exists in ZInQKernel, and syntax/templates/template-abs.md is not formalized (it has
  no `statement:` field).
- **Fix.** Either move the "Consequently" sentence into syntax/templates/template-abs.md, which
  already states it (line 13), or keep it and drop `proof: formalized` until the template exists.
  The intended statement, once the template is defined as a Lean term `valueAbs : ExPoly`, is:
  ```lean
  theorem rel_valueAbs (x a : ℚ) : valueAbs.Rel ![x, a] ↔ a = |x|
  ```
  It follows from the compilation theorem and `eq_abs_iff_four_squares`.

## Lesser remarks

### Hypotheses and target (rechecked against diophantine_zq.tex and docs/kernel-audits/hypothesis-audit.md)

- **FrozenTarget.** It is identical to upstream (`check_target.py` passes). `hyperoperation 4 2 n`
  is `2↑↑n`, with `2↑↑1 = 2`.
- **H (Theorem 4.1, tex 377–404).**
  - Every constant matches. `M_S(u)` equals `contactSupport`, as `prime_dvd_contactSupport_iff`
    shows. Junk values are excluded because `u ∉ 𝒞`.
  - The quantifier order is ∀S ∀R ∀u.
  - Lean lets `R` be any real with `R ≥ max(D, max S, 10¹²)`. This matches the manuscript's "every
    such S, R" and "every permitted larger R". The smallest admissible `R` is an integer and `H₆`
    increases with `R`, so the real form is not stronger than the integral one.
- **PC (Theorem 5.2, tex 973–1018).** `polePoly` matches term by term. Both inequalities are
  strict. `IsSquare B.den` is taken on the reduced denominator, and `v_p(B) ≥ 4` uses
  `padicValRat` with `B > 0`.
- **22P (Prop. 6.2, tex 1267–1300).**
  - `patternValues` gives the 22 values with `u₃ = Av − u₁ − u₂`.
  - In `GoodPatternPrime`, `p` odd with `r² = 2` means `p` splits in `ℚ(√2)`, and `75 ∓ 53r ≠ 0`
    means both reductions are good (the discriminant is `64d⁶`).
  - `cataloguePrime` never takes a junk value (`cataloguePrime_spec`).
  - The quantifiers are correct: ∀A ∀B₀ ∃u₁ u₂ v with `v ≠ 0`, then each value has its own ε, k, p.
- **CAT (Prop. 12.1, tex 6285–6361).** It asks for ≥ 22 primes in `Ioo 324 (2^(W³))`, which is
  weaker than what the manuscript proves. `cataloguePrime_lt_of_catalogueBound` gives the bound
  `H_max < X` that the manuscript uses.
- **MW.** `-genD ^ 2` parses as `-(d²)`, and `MordellWeilE` is now proved (`mordellWeilE`).

I agree with every verdict in hypothesis-audit.md.

### Sanity lemmas checked in a scratch file (since deleted)

```lean
example : MordellWeilE := mordellWeilE
example : codeP0 = iota 1 := by rw [iota_one]; rfl
example : codeNegP0 = iota (-1) := by
  rw [iota_neg, iota_one]; funext i; fin_cases i <;> simp [negCode, codeNegP0] <;> norm_num
-- the positivity gadget rejects 0
example : ¬ ∃ z : Fin 4 → ℚ, (0:ℚ) * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) = 1 :=
  fun h => (lt_irrefl (0:ℚ)) ((pos_iff_four_squares 0).2 h)
-- the absolute-value gadget rejects a = -2 for x = 2, although a² = x²
example : ¬ ∃ z : Fin 4 → ℚ, (-2:ℚ) = z 0^2 + z 1^2 + z 2^2 + z 3^2 ∧ (-2:ℚ)^2 = 2^2 := by
  rw [← eq_abs_iff_four_squares]; norm_num
```

All of them compile. (In the `codeNegP0` example I first omitted the final
`<;> norm_num`, and its two leftover goals were `15465/4 = -(-15465/4)` and
`-87483/32 = -(87483/32)`; `norm_num` closes them.)

The point counts in `pointCounts_17_23` were also rechecked by hand:
- mod 17: `6² = 2`, `75 − 53·6 ≡ 12`, `−12² ≡ −8`, and 19 affine points (20 with O);
- mod 23: `5² = 2`, `75 − 53·5 ≡ 17`, `−17² ≡ −13`, and 23 affine points (24 with O).

The small-height search was replayed independently in exact arithmetic. It gives
`|𝒬| = 7004`, `|𝒳₁| = 111` and the seven survivors of `smallSurvivors`.

### Harmless differences worth recording

- **rank-one.md.** `exists_generator_E` existentially quantifies its own generator. The article
  says the E decomposition holds "with θ⁻¹(S)" for the same S as on C. The proof uses
  `theta.symm S`, but the statement does not record it. A joint statement would be:
  `∃ S : curveC.toAffine.Point, ¬IsOfFinAddOrder S ∧ (∀ P, ∃! mT : ℤ × {T // 2•T = 0}, P = mT.1•S + mT.2) ∧ (∀ P : genCurve.toAffine.Point, ∃! mT : ℤ × {T // 2•T = 0}, P = mT.1•theta.symm S + mT.2)`.
  Also, `exists_generator_C`/`_E` still take `hMW : MordellWeilE`; `exists_generator_C'` is the
  unconditional form.
- **template-semantics.md and division-polynomials.md.** `Node.denote` interprets
  `fixed`/`psi`/`guard` through an abstract `Constructors E` record, and no instance with
  `psiComponent` exists yet. This is documented in Nodes.lean and harmless for now. A future
  bridge needs `specConstructors : Constructors FixedExpr := ⟨FixedExpr.val, psiComponent, guardPoly⟩`
  and a `rfl` lemma for `.psi` nodes before any theorem about the saved specification is stated.
- **Junk values in template-semantics.md.** Missing node or template references read as 0 or the
  empty polynomial, and `v − p` is `Nat` subtraction. Both are documented, and well-formed
  specifications never reach them.
- **Variable names.** `ZInQ.Syntax.Pair.delta` is `d² = 11243 − 7950s`, not `δ = 3 − s`
  (`ZInQ.delta`). They live in different namespaces and do not clash, but the names invite
  confusion.
- **Unused hypothesis.** In `duplication_common_divisor` the gcd-maximality hypothesis is unused,
  so the theorem is stronger than the article.
- **Search box bounds.** `search_box` states `|b| ≤ 162`, `|c| ≤ 81` and `k ≤ 162`, matching the
  article; the proof yields 161, 80 and 161.

### Incomplete `lean:` lists (all proposed names exist and say the article's claim)

- **point-codes.** `IsCanonicalCode`, `IsCarrierCode`, `carrierD`.
- **point-code-properties.** `pointCode_apply_zero`, `pointCode_apply_zero_eq_one_iff`,
  `pointCode_neg`, `iota_zero`, `iota_neg`, `iota_one`.
- **generator-curve.** `genD_sq`, `norm_genD`, `genCurve_Δ_ne_zero`, `genCurve_isElliptic`.
- **generator-point-equation.** `genY0_ne_zero`, `genP0_curve`.
- **integers-pid.** `Zs.euclideanDomain`, `IsPrimeReps.exists_factorization`,
  `IsPrimeReps.vp_eq_of_factorization`, `vp_mul`, `min_le_vp_add`, `vp_add_eq_min_of_ne`.
- **quadratic-field.** `K0.norm_eq`, `K0.trace_eq`, `K0.embPlus`, `K0.embMinus`,
  `K0.TotallyPositive`, `K0.signVector`.
- **special-primes.**
  - Quotients and residues: `quotSqrt2Equiv`, `quotGenDEquiv`, `not_isSquare_neg_one_mod_genD`.
  - Units and valuations: `deltaZ_eq`, `vS_genD`, `vS_delta`, `vS_epsilon`.
  - Total positivity: `totallyPositive_genD`, `totallyPositive_delta`.
- **units.** `Zs_unit_eq`, `unit_sqClass_iff`, `signVector_epsilon` and the other sign-vector
  lemmas.
- **division-polynomial-multiples.** `mulByN_formulas_of_charZero`. It is the "any field of
  characteristic zero" sentence, and slightly stronger than the article.
- **coordinate-change.** `epsilon_pow_four`, `epsilon_pow_six`,
  `delta_eq_epsilon_pow_four_mul_genD`, `theta_symm_some`, `theta_genT0`, `theta_genTd`,
  `theta_genTnegd`.
- **first-descent-image.** `kummer_genT0`, `kummer_genTd`, `kummer_genTnegd`,
  `kummer_theta_symm_pointR`, `card_descentGroup`.
- **descent-index.** `card_descentGroup`.
- **point-r-certificate.** `pointR_curve`, `two_sqrt2_ne_zero`, `pointR_slope`, `two_smul_pointR`.
- **reduction-point-counts.** `card_point_17`, `card_point_23`.
- **reduction-torsion.** `red_injOn_of_coprime`, `card_dvd_of_coprime`.
- **kummer-map.** `phiE`, `phiHatE`.
- **torsion.** `mem_torsion_C_iff`, `card_torsion_C`, and the new `not_isOfFinAddOrder_genP0`.
- **canonical-height-bounds.** `canonHeight_neg`, `canonHeight_nonneg`.
- **duplication-forms.** `two_smul_C_of_y_eq_zero`.
- **duplication-archimedean.** `duplication_bounds_emb`.
- **x-height-formula.** `hK0_nonneg`.
- **height-comparisons.** `log_height_comparison_one`, `log_height_comparison_two`.
- **r-torsion-translates.** `pointR_eq`.
- **field-pair-arithmetic.** Replace the list with:
  - part 1: `Pair.val_add`, `Pair.val_neg`, `Pair.val_smul`, `Pair.val_mul`, `Pair.val_conj`, `Pair.C_ev_norm`;
  - part 2: `holds_feq`;
  - part 3: `exists_update_fnz_iff`;
  - part 4: `exists_update_divFormula_iff`;
  - part 5: `exists_update_zFormula_iff`, `holds_ixFormula`;
  - the branch-exclusivity remark: `not_isO_and_fin`.

  Drop `holds_curve`, which is not a claim of this article.
- **nonzero-gadgets.** `eq_one_div_of_mul_eq_one`, `K0_ne_zero_iff_pairNorm`,
  `exists_update_nzFormula_iff`.
- **call-semantics.** `ExPoly.ev_call`, the displayed formula verbatim.
- **existential-lifting.** `Formula.lift_congr`.
- **field-pair-gadgets.**
  - Pair arithmetic: `Pair.mul`, `Pair.norm`, `Pair.conj`, `Pair.A`.
  - Formulas: `feq`, `Build.fnz`, `peq`, `isO`, `fin`, `curve`, `ixFormula`.
  - Codes: `Code.O`, `Code.neg`.
  - Generator: `Build.gen`.
- **rational-constants.** `codeP0_coordinates`.
- **division-polynomials.** `psiComponent_eval`.

## Method

- I audited main/ and the hypotheses directly against the manuscript.
- The four other chapter groups were read in parallel by read-only reviewers, who ran no Lean.
- I then checked every flagged item myself:
  - the torsion gap and its proposed proof, compiled;
  - the absolute-value claim;
  - the `iota`/`codeP0` link, compiled;
  - the canonical-height normalization, search box and small-height search statements;
  - the real-place statements;
  - `TendstoPt`;
  - `ExPoly.Rel` and calls.
- Lean ran one process at a time, with the load below 40 throughout.
