# Report of nat-precision

Blueprint section `compiler/natural/precision/` (17 leaves). Lean modules in
`ZInQKernel/Compiler/Precision/`, root `ZInQKernel/Compiler/Precision.lean` (imported by
`ZInQKernel.lean`), namespace `ZInQ.Compiler.Precision`. All 17 leaves are proved: no `sorry`,
no `native_decide`. `#print axioms` on the main results gives only `propext`, `Classical.choice`,
`Quot.sound`. `lake build ZInQKernel` succeeds. Branch merged with `origin/wip/model-top`
for `genP0_not_isOfFinAddOrder`.

## Leaves

| Article | Lean name(s) | Module | Status |
| --- | --- | --- | --- |
| signed-encoding.md | `enc`, `dec`, `decode5` | Encoding | proved (definition) |
| signed-encoding-bijection.md | `dec_enc`, `enc_dec`, `even_enc_iff`, `abs_dec` (`natAbs_dec`), `encEquiv` | Encoding | proved |
| z-coordinate.md | `zPt`, `x_ne_zero_of_y_ne_zero`, `zPt_ne_zero`, `zPt_neg`, `Admissible`, `zIdx`, `epsIdx`, `epsIdx_pos`, `rRatio`, `rRatio_eq_half_trace` | ZCoordinate | proved |
| precision-height-constant.md | `Q0`, `A0`, `sixF`, `bound`, `contacts` (with `heightF0`, `heightD`, `heightG0`, `heightE0`, `heightBcm`, `heightCcm` from `Hypotheses/Height.lean`) | HeightConstant | proved (definition) |
| precision-height-constant-value.md | `A0_eq_heightH6`, `heightQ_heightD`, `max_heightD_heightPrimes`, `heightD_admissible`, `bound_eq_heightH6`, `sixContact_at_heightPrimes` | HeightConstant | proved |
| precision-relation.md | `accepts` (with `acceptsInt`, `EarlyTestsInt`, `CloseTestInt`, `PrecisionTestInt`, `accepts_iff`, `precisionTestInt_iff`) | Relation | proved (definition) |
| precision-guards.md | `admissible_of_ne_zero`, `accepts_iff_tests` (no hypothesis); `..._of` versions take `¬ IsOfFinAddOrder genP0` | Relation | proved |
| precision-threshold.md | `four_eps_lt_iff_nat`, `four_eps_lt_iff`, `four_eps_mul_pow_lt_one_iff` | Threshold | proved |
| saturated-arithmetic.md | `saturatedArithmetic` (items 1–5), `saturate_factorial_succ` (item 5); upstream `PrecisionArithmetic.saturate_*` | Saturation | proved |
| capped-power.md | `cappedArithmetic`; upstream `PrecisionAlgorithms.cappedMul`, `cappedPower`, `cappedPowerLoop` | Saturation | proved |
| capped-height-test.md | `NExpr`, `NExpr.eval`, `NExpr.capped`, `cappedFact`, `NExpr.eA` (and `eF0 … eC`), `NExpr.capped_eq`, `NExpr.capped_le`, `NExpr.eval_eA`, `cappedBound`, `cappedBound_eq`, `cappedBound_le`, `divFourLoop`, `divFourLoop_eq`, `precision_test_iff` | CappedTest | proved |
| norm-zero.md | `rat_eq_zero_of_sq_sub_two_sq`, `intNorm_ne_zero`, `K0.eq_zero_of_norm_eq_zero`, `Zs.norm_ne_zero`, `Zs.mul_star_eq_norm` | NormZero | proved |
| jacobian-formulas.md | `JTriple`, `JTriple.curveE`, `jdbl`, `jadd`, `jH`, `jΛ`; items 1–2 `curveE_jdbl(_mem)`, `curveE_jadd(_mem)`; items 3–6 `jdbl_affine`, `jadd_affine`; item 7 `jH_eq_zero_iff`, `jΛ_eq_zero_iff`; item 8 `rep_jneg`, `two_nsmul_of_Y_eq_zero`; branching law `jO`, `jdblB`, `jaddB`, `Rep`, `rep_jdblB`, `rep_jaddB` | Jacobian | proved |
| jacobian-generator.md | `Acoef`, `P0J`, `P0J_Y_sq`, `P0J_rhs`, `curveE_P0J`, `toK0_Acoef`, `P0J_affine`, `rep_P0J` | JacobianGenerator | proved |
| jacobian-scalar-multiplication.md | `jmulLoop`, `jmulNat`, `jmul`, `rep_jmulLoop`, `rep_jmul`, `curveE_jmul`, `jmul_Z_eq_zero_iff`, `jmul_eq_some`, `jmul_Y_eq_zero_iff`, `admissible_iff_jmul` | ScalarMul | proved |
| decision-program.md | `decide5` (with `decideInt`, `nuJ`, `normJ`, `epsU`, `epsV`, `ratioNum`, `ratioDen`, `capL`) | Decision | proved (definition, computable) |
| decision-program-correct.md | `decide5_iff`, `decideInt_iff` | DecisionCorrect | proved |

## Statement corrections and choices

- **jacobian-formulas, items 3–4.** Doubling needs `2 ≠ 0` in the field: in characteristic 2,
  `Z₃ = 2YZ = 0`, so `Y₃/Z₃³ = 0` while `λ(x - X₃/Z₃²) - y = -y`, and item 4 fails. `jdbl_affine`
  assumes `(2 : F) ≠ 0`; the branching group-law lemmas assume `[NeZero (2 : F)]`. Items 5–6 hold
  over any field. Items 3–6 also state `Z₃ ≠ 0` and, for addition, `x₁ ≠ x₂`.
- **jacobian-formulas, items 1–2.** These are exact identities with explicit cofactors:
  `𝓔(dbl P) = 64 Y⁶ 𝓔(P)`, and `𝓔(add(P₁,P₂)) = c₁ 𝓔(P₁) + c₂ 𝓔(P₂)` with
  `c₁ = Z₂⁶(U₁-U₂)³(A X₂ Z₁⁶ Z₂⁴ - X₁³Z₂⁶ + 3X₁X₂²Z₁⁴Z₂² - X₂³Z₁⁶ + Y₁²Z₂⁶ - 2Y₁Y₂Z₁³Z₂³)` and the
  symmetric `c₂` (`addCofactor₁`, `addCofactor₂`). Ideal membership follows from them.
- **jacobian-formulas, item 7.** `Λ = 0 ↔ y₁ = y₂` holds whenever `Z₁Z₂ ≠ 0`; it does not need
  `H = 0`. The point-level consequences (doubling if `Λ = 0`, `O` otherwise) are proved inside
  `rep_jaddB` using Mathlib's `Y_eq_of_X_eq`.
- **jacobian-scalar-multiplication.** `dbl*` and the `H = 0, Λ ≠ 0` branch return the fixed
  triple `O = (1, 1, 0)`; the article's "`O ↦ O`" is read as "return `O`". "Represents" is the
  predicate `JTriple.Rep A T P` over a field (stated for `shortCurve A`, which is `genCurve` for
  `A = -d²`), applied to the image of `mul(k)` under `ℤ[s] → K₀`.
- **z-coordinate.** `zPt`, `zIdx`, `epsIdx`, `rRatio` are total functions with junk value `0` at
  `O` (and `-x/0 = 0` at points of order two); only their values at admissible indices are used.
  `r(a,j) = ½ Tr(z_j/z_a)` is `rRatio_eq_half_trace`, with `QuadraticAlgebra.trace`.
- **precision-height-constant-value.** "`𝓑(n, κ)` is the bound `B(n, κ)` of the ordinary-value
  relation" is stated as `bound_eq_heightH6 : 𝓑(n, κ) = H₆(D) |κ F(n)|²⁴` in `ℝ`, since the
  ordinary-value relation is not defined in this section. `S_ht` is `heightPrimes`
  (primes `≤ 324` as a `Finset ℕ`). The max statement is `max_heightD_heightPrimes`, using
  `S_ht.sup id ≤ 324` rather than the exact value 317. I added `sixContact_at_heightPrimes`
  (hypothesis H at `S = S_ht`, `R = D`) for the assembly chapter.
- **precision-relation.** The precision test is `4 ε_l · 4^𝓑 < 1` in `ℚ` (`PrecisionTestInt`).
  The form `4 ε_l < 4^(-𝓑)` is `precisionTestInt_iff`. `𝒞` is the integer `Finset`
  `contacts`; `cast_mem_contactSet_iff` relates it to the hypothesis file's `contactSet ⊆ ℚ`, and
  `sixF_eq_zero_iff` gives `F(n) = 0 ↔ n ∈ 𝒞`.
- **precision-guards.** Now unconditional, through `genP0_not_isOfFinAddOrder` from
  `origin/wip/model-top` (merged). The versions with an explicit hypothesis remain as
  `admissible_of_ne_zero_of` and `accepts_iff_tests_of`.
- **saturated-arithmetic / capped-power.** These reuse the upstream definitions (`saturate`,
  `cappedMul`, `cappedPower`), which match the articles exactly. Each article gets one bundled
  theorem (`saturatedArithmetic`, `cappedArithmetic`).
- **decision-program.** This is a computable `def`. Its sequence of tests and quantities is
  exactly the article's. A sanity `#eval` (not committed) gives `(jmul 2).Z = 2·Y₀·Z₀` and, as
  expected, `false` on small inputs.

## Lemmas added beyond the leaves

- Unfolding the hypothesis-file constants: `degFn`, `e0Fn`, `bcmFn`, `ccmFn`, `qFn`, `h6Fn`,
  `heightD_eq`, `heightE0_eq`, `heightBcm_eq`, `heightCcm_eq`, `Q0_eq`, `A0_eq`, `A0_pos`,
  `ten_pow_twelve_le_heightD`, `heightF0_le_heightD` (see Problems).
- `cappedFact_eq`, `saturate_factorial_saturate`, `one_le_divFourLoop_saturate_iff`.
- `JTriple.map` and its compatibility with `jdbl`, `jadd`, `jdblB`, `jaddB`, `jmulLoop`
  (`map_jaddB` etc., for injective ring maps); `curveE_jdblB`, `curveE_jaddB`,
  `curveE_jmulLoop`; `chord_aux`, `some_eq_some_of`, `Rep.congr_point`, `Rep.eq_zero_iff`.
- For the correctness proof: `toK0_star`, `toK0_norm`, `K0.intCast_re/_im`, `K0.div_intCast`,
  `zIdx_eq_nu` (`z_k = ν_k / N_k`, `N_k ≠ 0`), `nuJ_ne_zero`, `epsIdx_eq` (`ε_l = U/V`),
  `rRatio_eq` (`r = θ/δ`), `closeTest_iff`, `precisionTest_iff`.

## Problems

- **The kernel cannot unfold `heightD` (or `heightE0`, `heightBcm`, `heightCcm`) against its
  displayed body.** Both `theorem : heightD = heightF0 * 3 ^ (256 * heightF0 ^ 4) := rfl` and
  the auto-generated equation lemma used by `unfold`/`rw [heightD]` fail with "the kernel refused
  to evaluate `Nat.pow`". The kernel unfolds the `HMul.hMul` side first (an abbreviation),
  reaches `Nat.mul`, and its GMP literal reduction then evaluates `3 ^ (256·F₀⁴)`. What works:
  compare the constant with a function application of the **same definitional height**. The
  kernel then unfolds both sides at once and finds them syntactically equal. For example
  `heightD = degFn heightF0 := rfl` with `degFn f := f * 3 ^ (256 * f ^ 4)` (both have height 7).
  For `heightE0`, `heightBcm`, `heightCcm` the function body carries an unused `let` of
  `heightD`/`heightBcm` to reach the same height. The usable equations are `heightD_eq`,
  `heightE0_eq`, `heightBcm_eq`, `heightCcm_eq` in `HeightConstant.lean`; other tasks should use
  them rather than unfold these constants. My own constants `Q0` and `A0` are defined as
  `qFn heightD heightE0` and `h6Fn heightCcm Q0`, so their equation lemmas are safe.
- Two related traps. First, `simp` on closed expressions that contain these constants (the
  first proof of `eval_eC`) can leave a kernel check that evaluates them; rewriting with `rw`
  works. Second, closing a goal with a lemma whose `^` instance differs from the goal's (for
  example `Nat.pow_pos` against a `Monoid.npow` power) makes the kernel compare the instances
  by unfolding the powers. Use `positivity`, or lemmas that match syntactically.
- The generic Field lemmas about `(shortCurve A).toAffine.Point` produce terms whose
  `CommRing K0` instance is `QuadraticAlgebra.instField.toCommRing`, while `genCurve` points use
  `QuadraticAlgebra.instCommRing`. They are defeq, but `rw` cannot match across them. I used
  `exact`/`Rep.congr_point` with statements elaborated on the `genCurve` side.

## Suggestions for the next agent

- The assembly and translation chapters should use `accepts` (or `acceptsInt`), `enc`/`dec` and
  `bound` from here. `decide5_iff` is the bridge from the program to the relation. The
  primitive-program and lowering chapters still have to show that their precision program
  computes `decide5`.
- The scalar loop is generic (`jmulLoop` over any commutative ring with decidable equality,
  plus `rep_jmulLoop` over a field of characteristic ≠ 2), so it can be reused for other base
  points.
- If the hypothesis file is ever edited, defining `heightD`, `heightE0`, … through parametric
  functions (as upstream's `HeightConstantComparison` does: `d := degreeFromBase d0`) would
  remove the need for the height-matching workaround.
