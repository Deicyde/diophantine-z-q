# model-field report

Task: basic objects of the elliptic model (blueprint `model/field/`, plus `model/point-codes.md`
and `model/descent/{coordinate-change,point-r-certificate}.md`).
Root module `ZInQKernel/Model/Field.lean` (imported from `ZInQKernel.lean`); modules in
`ZInQKernel/Model/Field/`. Everything is proved; no `sorry`, no `native_decide`, no axioms
(`#print axioms` on the main results: `propext, Classical.choice, Quot.sound` only).
Finite computations are `decide` (residues mod 4 and 7, small `ℤ[s]` identities) or
`norm_num` on the two rational components of `K₀` identities.

## Status

| article | Lean name(s) | status |
| --- | --- | --- |
| model/field/quadratic-field.md | `K0`, `sqrt2` (reused); `K0.embPlus`, `K0.embMinus`, `K0.norm_eq_embPlus_mul_embMinus`, `K0.TotallyPositive`, `K0.signVector`, `K0.norm_eq`, `K0.trace_eq`, `K0.star_eq'`, `K0.mk_mul_mk'`, `epsilon`, `delta`, `Zs`, `Zs.toK0`, `instance NumberField K0`, `finrank_K0`, `instance IsFractionRing Zs K0`, `exists_eq_div_Zs` (Basic.lean) | proved |
| model/field/generator-curve.md | `genCurve_eq_shortCurve`, `genD_sq`, `neg_genD_sq`, `norm_genD`, `genCurve_Δ`, `genCurve_isElliptic`, `genT0`, `genTd`, `genTnegd`, `genCurve_two_torsion` (Curve.lean) | proved |
| model/field/generator-point-equation.md | `genP0_curve`, `genY0_ne_zero`, `genP0_equation` | proved |
| model/field/generator-point.md | `genX0`, `genY0`, `genX0_eq`, `genY0_eq`, `genP0`, `genP0_ne_zero` | proved |
| model/point-codes.md | `pointCode`, `iota` (noncomputable), `carrierD`, `IsCanonicalCode`, `IsCarrierCode`, `iota_injective_of_addOrderOf_eq_zero` (Codes.lean) | proved |
| model/field/point-code-properties.md | `pointCode_injective`, `pointCode_apply_zero`, `pointCode_apply_zero_eq_one_iff`, `negCode`, `pointCode_neg`, `pointCode_neg_apply`, `iota_zero`, `iota_neg`, `iota_one`, `iota_add` | proved |
| model/field/special-primes.md | `prime_sqrt2Z`, `two_eq_sqrt2Z_sq`, `residueTwo`, `ker_residueTwo`, `quotSqrt2Equiv`, `vS_rat`, `vS_rat_mul_sqrt2`, `vS_formula`, `v2Top`, `vS_formula_withTop`, `norm_genDZ`, `prime_genDZ`, `residueSeven`, `ker_residueSeven`, `quotGenDEquiv`, `not_isSquare_neg_one_mod_genD`, `epsilonZ_pow_four`, `deltaZ_eq`, `delta_eq_epsilon_pow_four_mul_genD`, `associated_genDZ_deltaZ`, `prime_deltaZ`, `vp_genDZ_eq_vp_deltaZ`, `vS_genD`, `vS_delta`, `vS_epsilon`, `vp_genDZ_sqrt2`, `vp_genDZ_two`, `totallyPositive_genD`, `totallyPositive_delta` (SpecialPrimes.lean) | proved |
| model/field/residue-checks.md | `residues_mod_seven`, `not_isSquare_neg_one_zmod_seven` (Residues.lean) | proved (`decide`) |
| model/field/dyadic-valuation.md | item 1: `vS_sq_add_one`; item 2: `val_s_sq_add_delta_sq`; integral cores `vS_sq_add_odd_sq`, `vS_sq_add_sq`, `vS_mk_eq_two`, `vS_mk_eq_three` (Dyadic.lean) | proved |
| model/field/integers-pid.md | `Zs.euclideanDomain`, `Zs.isPrincipalIdealRing`, `Zs.uniqueFactorizationMonoid` (Euclidean.lean); `vp`, `vp_mul`, `vp_inv`, `vp_div`, `vp_pow`, `vp_zpow`, `vp_neg`, `min_le_vp_add`, `vp_add_eq_min_of_ne`, `le_vp_iff_pow_dvd`, `vp_eq_iff`, `vp_self`, `vp_unit`, `vp_eq_of_associated` (Valuation.lean); `IsPrimeReps`, `exists_isPrimeReps`, `IsPrimeReps.exists_factorization`, `IsPrimeReps.vp_eq_of_factorization` (Factorization.lean) | proved |
| model/field/units.md | `epsUnit`, `norm_epsilonZ`, `Zs.isUnit_iff_norm`, `Zs_unit_eq`, `Zs_unit_sqClass`, `signVector_one/neg_one/epsilon/neg_epsilon`, `signVector_mul_sq`, `unit_sqClass_iff`, `isSquare_of_totallyPositive_unit` (Units.lean) | proved |
| model/descent/coordinate-change.md | `curveC`, `curveC_isElliptic`, `epsilon_pow_four`, `epsilon_pow_six`, `epsilon_inv`, `norm_epsilon`, `neg_delta_sq_eq`, `theta : genCurve.toAffine.Point ≃+ curveC.toAffine.Point`, `theta_some`, `theta_symm_some`, `cT0`, `cTdelta`, `cTnegdelta`, `curveC_two_torsion`, `theta_genT0`, `theta_genTd`, `theta_genTnegd`, `two_nsmul_theta_eq_zero_iff` (CurveC.lean) | proved, except the Kummer-map clause (see corrections) |
| model/descent/point-r-certificate.md | `pointR_curve`, `two_sqrt2_ne_zero`, `pointR`, `pointR_slope`, `twoRX`, `twoRY`, `two_smul_pointR`, `epsilon_pow_four_mul_genX0`, `epsilon_pow_six_mul_genY0`, `epsilon_inv_pow_four_mul_twoRX`, `epsilon_inv_pow_six_mul_twoRY`, `theta_genP0`, `theta_symm_two_smul_pointR` | proved |

## Statement corrections and choices

- **dyadic-valuation, item 1.** Mathlib's `padicValRat 2 0 = 0`, so the article's hypothesis
  "`v₂(B) ≥ 0`" and case split "`v₂(B) ≥ 1` / `v₂(B) = 0`" (with `v₂(0) = ∞`) are stated as
  `B = 0 ∨ 0 ≤ v₂ B`, case `B = 0 ∨ 1 ≤ v₂ B` (value 2) and case `B ≠ 0 ∧ v₂ B = 0` (value 3);
  `v₂(A) = 0` is `A ≠ 0 ∧ padicValRat 2 A = 0`. With the junk value read literally, `B = 0` would
  fall in the wrong case.
- **special-primes, v_s formula.** Stated three ways: `vS_rat` (`c₁ = 0`), `vS_rat_mul_sqrt2`
  (`c₀ = 0`), `vS_formula` (both nonzero), and a single `WithTop ℤ` statement
  `vS_formula_withTop` with `v2Top c = ⊤` for `c = 0`, which is the article's formula verbatim.
- **Valuations.** `vp π : K₀ → ℤ` for `π : Zs` is `-log` of Mathlib's
  `HeightOneSpectrum.valuation` at `(π)`, with junk values `vp π 0 = 0` and `vp π = 0` when `π`
  is not prime. Lemmas that need it take `Prime π`. `v_s` is written `vp sqrt2Z` (an
  abbreviation `vS` blocked `rw`, so it was dropped; lemma names keep the `vS_` prefix).
- **integers-pid, factorization.** "π running over a set of representatives" is the structure
  `IsPrimeReps P` (all elements prime, every prime associated to exactly one element of `P`);
  `exists_isPrimeReps` constructs one. Factorization uses a finite `S ⊆ P` containing the support
  of `v_·(x)`, with uniqueness `IsPrimeReps.vp_eq_of_factorization`.
- **units, item 2.** "The unit squareclasses are exactly the four classes of `1, -1, ε, -ε`" is
  `Zs_unit_sqClass` (every unit is `w²`, `-w²`, `εw²` or `-εw²`) together with `unit_sqClass_iff`
  (two units are in the same class iff they have the same sign vector) and the four sign-vector
  values. Item 3 returns `∃ w : Zsˣ, u = w ^ 2`.
- **coordinate-change.** The clause `α_{-δ²}(θ(P)) = α_{-d²}(P)` is not formalized. The Kummer
  map `α_b` is defined in `model/descent/kummer-map.md`, which the descent agent owns. The
  ingredients are here: `theta_some` (abscissas are multiplied by `ε⁴ = (ε²)²`) and
  `neg_delta_sq_eq : -δ² = (ε²)⁴ (-d²)`, so the `(0,0)` classes agree modulo squares.
  `curveC` is defined directly as `shortCurve (-delta ^ 2)`, not as `Descent.curveB (-delta^2)`
  as the notes suggest. If the descent agent defines `curveB b` with `a₄ = b` and the other
  coefficients 0, it unfolds to the same structure.
- **generator-curve, two-torsion.** Stated with named points
  `2 • P = 0 ↔ P = 0 ∨ P = genT0 ∨ P = genTd ∨ P = genTnegd` instead of the notes' set form. The
  group law is Mathlib's; its formulas (`Point.add_some`, `slope`, `addX`, `addY`) are not
  restated.
- **point-codes.** "Since `P₀` has infinite order, distinct indices have distinct codes" depends
  on Proposition 3.1, so it is stated conditionally:
  `iota_injective_of_addOrderOf_eq_zero (h : addOrderOf genP0 = 0)`. `pointCode_neg` uses
  `negCode c = ![c 0, c 1, c 2, -c 3, -c 4]`; `pointCode_neg_apply` is the notes' `if` form.

## Lemmas added beyond the leaves

- `ShortWeierstrass.lean`: generic `shortCurve A : y² = x³ + A x` over any field;
  `shortCurve_equation_iff`, `shortCurve_Δ`, `shortCurve_isElliptic`,
  `two_nsmul_some_eq_zero_iff` (any Weierstrass curve), `shortCurve_two_nsmul_some_eq_zero_iff`,
  and the scaling isomorphism `scaleEquiv (hu : u ≠ 0) (hB : B = u⁴ A) : E_A ≃+ E_B`,
  `(x, y) ↦ (u² x, u³ y)`, with additivity proved (`scalePoint_add`, `shortCurve_slope_scale`).
  `theta` is `scaleEquiv` at `u = ε²`. The descent agent can reuse it for `λ_b`
  (`E_{16b} → E_b`, `u = 1/2`).
- `genCurve_eq_shortCurve : genCurve = shortCurve (-genD ^ 2)` (by `rfl`), and instances
  `IsElliptic` for both spellings.
- `Zs` API: `Zs.norm_eq`, `Zs.norm_toK0`, `Zs.norm_eq_zero_iff`, `Zs.intCast_dvd_iff`,
  `sqrt2Z_dvd_iff`, `genDZ_dvd_iff`, `Zs.prime_of_natAbs_norm_prime`, the elements
  `sqrt2Z genDZ epsilonZ deltaZ` with `toK0_*` simp lemmas.
- `attribute [simp] QuadraticAlgebra.re_ofNat im_ofNat re_one im_one` (global, in Basic.lean):
  `ext <;> simp ...; norm_num` then evaluates explicit `K₀` arithmetic.
- `instance : Algebra Zs K0`. Mathlib's instance is for `QuadraticAlgebra ℚ ↑2 ↑0` (integer
  casts), which instance search does not identify with `K0 = QuadraticAlgebra ℚ 2 0`; it is
  re-exported with `inferInstanceAs`, and likewise `IsFractionRing Zs K0`.

## Problems

- **Pushing failed during the whole session.** github.com resets the connection from this host
  (`Recv failure: Connection reset by peer`), and the fwdproxy returns 403 for GitHub. All
  commits are on the local branch `wip/model-field` in `~/dzq-wt/model-field`, not on the remote.
  Someone with network access must push, e.g. `git push origin HEAD:wip/model-field` from that
  worktree.
- Type mismatch between `genCurve` and `shortCurve (-genD ^ 2)`: they are defeq but not
  reducibly, so `rw` with `scaleEquiv_*` lemmas fails on `theta`. Use `exact` with
  `scaleEquiv_some_eq`, or the specialized `theta_some`/`theta_symm_some`.

## Suggestions for the next agent

- Descent: the Kummer clause of coordinate-change follows in a few lines from `theta_some` and
  `neg_delta_sq_eq` once `α_b` exists. `curveC_two_torsion` and `genCurve_two_torsion` give the
  two-torsion; `vp`, `prime_genDZ`, `prime_sqrt2Z`, `Zs_unit_sqClass`,
  `isSquare_of_totallyPositive_unit`, `not_isSquare_neg_one_mod_genD` and `val_s_sq_add_delta_sq`
  are the arithmetic inputs.
- Heights: `instance NumberField K0`, `K0.embPlus/embMinus` and `genP0`, `pointR`,
  `two_smul_pointR` are available.
- Never unfold `iota` on concrete large indices; use `iota_add`, `iota_neg`, `iota_one`.
