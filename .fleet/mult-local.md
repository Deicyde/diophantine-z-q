# mult-local report

Task: the local theory at finite places for the multiplication chapter
(blueprint `multiplication/local/`, 13 leaves). Root module `ZInQKernel/Multiplication/Local.lean`
(imported from `ZInQKernel.lean`). Modules are in `ZInQKernel/Multiplication/Local/`. All
declarations are in namespace `ZInQ.Mult`. There are no axioms, no `native_decide` and no `sorry`
in definitions. The finite checks use `decide` or `norm_num`.

The branch merges `origin/wip/model-descent`. It reuses that branch's chord algebra
(`vieta_shortCurve`, `sum_t_identity`, `tw_equation`) and its torsion theorem
(`two_nsmul_eq_zero_of_isOfFinAddOrder`). `lake build ZInQKernel` succeeds.
`#print axioms` on every theorem marked "proved" gives only `propext, Classical.choice, Quot.sound`.

## Status

| article | Lean name(s) | status |
| --- | --- | --- |
| local/formal-group.md | `formal_val_x_y` (part 1), `formalFilt` / `formalNbhd` / `mem_formalNbhd_iff` / `coe_formalNbhd` (part 2), `zCoord_injOn` (part 3), `zsmul_mem_W1`, `zsmul_mem_formalFilt` (part 4); data `W1`, `InW1`, `zCoord`, `wCoord`, `omegaCoord` (FormalGroup.lean); chord estimate `chord_add` (Chord.lean) | proved |
| local/primes-above-p.md | `primeR_split`, `quotPrimeREquiv`, `ker_residueAt` (part 1, split case); `primeP_inert` (part 1, inert case); `vp_ratCast` (part 2); `vp_star`, `prime_star` (part 3); `vp_trace_ge` (part 4) (PrimesAbove.lean) | proved |
| local/generator-dyadic-numerals.md | `genP0_dyadic_numerals`, closed form `genP0_dyadic_numerals_closed` (Dyadic.lean) | proved |
| local/dyadic-generator.md | `genP0_val_s`, `genP0_mem_formalFilt_three`, `zsmul_genP0_mem_formal`; `vS_genX0`, `vS_genY0` (Dyadic.lean) | proved |
| local/logarithm-series.md | `uSeries_eq`, `uSeries_unique`, `one_sub_uSeries_sq`, `X_mul_uSeries`, `uSeries_genE_unit` (part 1); `invDiffSeries_sq`, `invDiffSeries_mul`, `X_mul_derivative_uSeries`, `invDiffSeries_ode` (part 2); `derivative_formalLog`, `coeff_formalLog_genE` (part 3) (LogSeries.lean) | proved |
| local/logarithm-coefficients.md | `log25_coefficients`, `log25Coeff_list`, `sixteen575_factor`, `genD_sq_eq`, `truncLog`, `truncLog_eq`, `truncLog_eq_trunc` (LogCoefficients.lean); `truncLog_eq_partialLog` (TruncationError.lean) | proved |
| local/truncation-unit.md | `truncLog_eq_mul_unit`, `truncLog_ne_zero` (generic); `log25_eq_mul_unit`, `log25_ne_zero` (at every prime of `ℤ[s]`); `log25_eq_mul_unit_completion`; `vp_16575_le_two` (TruncationUnit.lean) | proved |
| local/truncation-error.md | `log25_truncation_error`, `log25_truncation_zero`; generic `partialLog_truncation_error` (TruncationError.lean) | proved |
| local/formal-group-law.md | part 1: `omegaSeries`, `omegaSeries_eq`, `omegaSeries_unique`, `omegaSeries_lowCoeffs`, `omegaSeries_integral`, `omegaSeries_hasSum` (`-1/y = ω(-x/y)`, convergent) (proved); part 2: `formalAdd` (definition), `formalGroupLaw_exists` (**sorry**) (FormalGroupLaw.lean) | part 1 proved; part 2 statement only |
| local/formal-logarithm.md | `formalLog`, `logCoeffA`, `invDiffCoeff`, `invDiffSeries` (definitions, FormalLog.lean); `invDiffCoeff_spec`, `derivative_formalLog` (proved); `formalLog_formalAdd` (**sorry**); `summable_log` (convergence, proved); `evalLog`, `ellLog` (definitions); `ellLog_add` (**sorry**); `ellLog_zsmul`, `ellLog_neg`, `ellLog_zero` (proved, `ellLog_zsmul` from `ellLog_add`) (FormalLogarithm.lean) | statement only (convergence and derivative proved) |
| local/logarithm-isometry.md | `evalLog_isometry` (part 1, proved without sorry); `ellLog_val_eq` (proved without sorry); `ellLog_injOn`, `val_z_zsmul_eq`, `ellLog_unramified` (part 2 and the odd unramified case; their own proofs have no sorry but use `ellLog_add`) (FormalLog.lean, FormalLogarithm.lean) | part 1 proved; part 2 proved from `ellLog_add` |
| local/logarithm-ratio.md | `ellLog_ratio` (Ratio.lean); its own proof has no sorry but uses `ellLog_add` | proved from `ellLog_add` |
| local/logarithm-nonvanishing.md | `log25_z_ne_zero`; `genP0_not_isOfFinAddOrder`, `zsmul_genP0_ne_zero` (Nonvanishing.lean) | proved |

The three `sorry`s are `formalGroupLaw_exists`, `formalLog_formalAdd` and `ellLog_add`. Only `ellLog_add` is used downstream, by `ellLog_zsmul`, `ellLog_injOn`,
`val_z_zsmul_eq`, `ellLog_unramified` and `ellLog_ratio`.

## Conventions and statement corrections

- **Valuations.** The generic statements use an additive valuation
  `v : AddValuation K (WithTop ℤ)`, which matches the articles' `v : K → ℤ ∪ {∞}`. Bridges:
  - `ordOf w`, for Mathlib's `w : Valuation K ℤᵐ⁰`, is `x ↦ -log w(x)`.
  - `vP π hπ = ordOf ((primeSpec π hπ).valuation K0)` is the valuation of `K₀` at a prime element
    `π`. It agrees with the model chapter's `vp π` off `0` (`vP_apply`, `le_vP_iff`).
  - `vK K = ordOf Valued.v` is the valuation of a `ℤᵐ⁰`-valued field.
  - `vComp π hπ` is the valuation of the completion `(primeSpec π hπ).adicCompletion K0`. On `K₀`
    it restricts to `vP` (`vComp_algebraMap`).

  `Vge v m x` abbreviates `m ≤ v x`.
- **formal-group.**
  - The hypotheses "`char K = 0`", "`v` normalized" and "`A ≠ 0`" are dropped: they are not
    needed, and Mathlib's group law exists on the nonsingular points of any Weierstrass curve.
    `v(A) ≥ 0` is the hypothesis `hA : 0 ≤ v A`.
  - `W_k(K)` (`formalFilt A hA k`) is defined for every `k : ℤ`. For `k ≤ 1` it equals `W₁(K)`
    (`formalFilt_eq_of_le_one`).
  - The chord estimate (`Chord.lean`) generalizes model-descent's `K₀`-specific
    `KernelReduction.lean` to any field and valuation. It uses `t = x/y = -z` and `w = 1/y = -ω`,
    and also gives `v(t(P₁+P₂) - t₁ - t₂) ≥ m + 1`.
- **primes-above-p.**
  - Primes are prime elements `π` of the PID `ℤ[s]`, with the model chapter's `vp π`.
  - Split case: data `r : ℤ` with `(r : ZMod p)^2 = 2`. Then `primeR p r = span {p, s - r}`, the
    residue map is `residueAt`, and `Zs ⧸ primeR p r ≃+* ZMod p` is `quotPrimeREquiv`.
  - Inert case: `Nat.card (Zs ⧸ (p)) = p²` comes from `Ideal.absNorm`.
  - Conjugation is `starRingEnd Zs` on ideals and `star` on elements. The conjugate prime of `π`
    is `star π`.
  - Part 2 holds for every `q ∈ ℚ`, because both sides are `0` at `q = 0`.
  - Part 4 concludes `Tr y = 0 ∨ m ≤ padicValRat p (Tr y)`. This is needed because
    `padicValRat p 0 = 0`.
- **dyadic-generator.** Stated over `K₀` with `vS = vP sqrt2Z prime_sqrt2Z`, as the notes suggest,
  and not in the completion `K_(s)`. To move it to `K_(s)`, use `vComp_algebraMap` together with
  `mapPt` and `zCoord_mapPt` (PointMap.lean).
- **logarithm-coefficients.** `truncLog δ z = Σ_{j<7} c_j δ^j z^{4j+1}` is defined over any
  commutative ring. Its coefficient list matches `log25Coeffs` of the syntax template
  `Pair.log25` on branch `wip/syntax-templates`, which is not on main. The lead still has to
  link the template's pair polynomial to `truncLog (genD ^ 2)`: both are the same loop
  `Σ c_j δ^j ζ^{4j+1}` with `δ = 11243 - 7950 s` (`genD_sq_eq`).
- **logarithm-nonvanishing, logarithm-ratio.** The articles assume Mordell–Weil only to know
  that `P₀` has infinite order. That fact is now unconditional by model-descent's torsion theorem
  (`genP0_not_isOfFinAddOrder`), so these statements take no MW hypothesis. In
  `logarithm-ratio`, points of `E(K₀)` are moved to `K_π` by `mapE π hπ`, which is `mapPt` along
  `algebraMap K0 K_π` (a group homomorphism, `mapE_zsmul`). Over `K_π`, `E` is
  `shortCurve (-genDAt π hπ ^ 2)` with `genDAt = algebraMap genD`.
- **formal-logarithm.**
  - Following the notes, the logarithm is defined explicitly:
    `formalLog A = Σ_{r≥1} b_{r-1} T^r / r`, with `b_{4j} = binom(2j,j) Aʲ` and `bᵢ = 0` otherwise.
    For `A = -d²` this is the article's binomial series (`coeff_formalLog_genE`).
  - "`d/dT log` is the expansion of `dx/2y`" is `derivative_formalLog` together with
    `invDiffSeries_mul`, `X_mul_derivative_uSeries` (logarithm-series). The `z`-expansion of
    `dx/(2y)` is `z u'/(2u) dz = dz/(1 - 2Az²u)`.
  - Residue characteristic `p` with `v(p) = e` is the structure `ResidueChar K p e`
    (`v(p) = e`, `v(n) = 0` for `p ∤ n`). For the completions it is `residueChar_completion`.
  - `ellLog P = evalLog A (zCoord P)` is a plain function, so that no `sorry` sits in a
    definition. Its homomorphism property is the theorem `ellLog_add`.
- **formal-group-law.**
  - `omegaSeries` is defined over any commutative ring. Over `𝒪 = Valued.integer K` it lies in
    `𝒪⟦T⟧` by construction, and `omegaSeries_integral` gives the valued-field form.
  - `formalAdd A` is the explicit chord series `T₁ + T₂ + 2Aλν(1 + Aλ²)⁻¹`, where
    `λ = Σ ω_{i+j+1} T₁ⁱ T₂ʲ` and the inverse is `MvPowerSeries.invOfUnit`.
  - Mathlib's `FormalGroup` structure contains associativity as a field, so it cannot be a
    definition here. Part 2 is the theorem `formalGroupLaw_exists`: there is an
    `F : FormalGroup 𝒪` with underlying series `formalAdd A`, `F.IsComm`, `F(T, -T) = 0`, and
    `HasSum (n ↦ F_n z(P)^{n₀} z(Q)^{n₁}) (z(P+Q))` on `W₁(K)`.
- **logarithm-isometry.**
  - Part 1 is `evalLog_isometry`, with the hypothesis `v(t) > e/(p-1)` written as
    `(e : ℤ) < (p - 1) * v(t)`.
  - Part 2 is stated on `formalFilt A hA k` for any `k` with `(p-1) k > e`. The least such `k`
    gives the article's subgroup.
  - `val_z_zsmul_eq` holds for all `n`, including `n = 0` (both sides are `⊤`), so `n ≠ 0` is
    dropped.
- **truncation-error.** Stated exactly as in the article: `v(ε) ≥ 28`, with `ε` in `K_π`. The
  proof gives `v(ε) ≥ 28·v(z)`.

## Lemmas added beyond the leaves

- `ValHelpers.lean`: the `Vge` calculus (`add`, `mul`, `pow`, `div_unit`, `div_val'`, `sum_of_le`,
  `val_one_add`, `val_add_eq`, `val_pow_coe`, `val_zpow_coe`, …).
- `Valuations.lean`: `ordOf`, `le_ordOf_iff`, `vP`, `vP_apply`, `le_vP_iff`, `vP_toK0_nonneg`.
- `Analytic.lean`, generic analysis in complete `ℤᵐ⁰`-valued fields:
  - `nonarchimedean_valued`: Mathlib has no `NonarchimedeanAddGroup` instance for `Valued`.
  - `exists_vge_subset`, `tendsto_zero_of_vK`, `tendsto_zero_of_vK'`, `summable_of_vK`,
    `summable_of_vK_cofinite`, `isClosed_vK_ge`, `isClosed_vK_gt`, `le_vK_tsum`, `lt_vK_tsum`,
    `le_vK_tsum_of_int`.
- `FormalLog.lean`: `ResidueChar.val_natCast`, `padicValNat_bernoulli` (`(p-1) v_p(r) ≤ r-1`),
  `two_mul_padicValNat_le`, `vge_logTerm`, `evalLog_sub_self`.
- `PointMap.lean`: `mapPt`, `mapPt_add`, `mapPtHom`, `zCoord_mapPt` (points of `y² = x³ + Ax`
  under a field embedding).
- `TruncationUnit.lean`: `vComp`, `vComp_algebraMap`, `vp_natPrime_le_one`,
  `vp_natCast_coprime`, `vP_16575_le_two`, `vP_genD_sq_nonneg`.
- `TruncationError.lean`: `charZero_completion` (instance), `residueChar_completion`, `genDAt`,
  `vComp_neg_genDAt_sq_nonneg`, `omitted_term_bound`.
- `PrimesAbove.lean`: `natCast_dvd_iff`, `prime_natCast_of_not_isSquare`,
  `not_sq_dvd_natCast` (odd `p` is unramified), `vp_natCast_self`, `vp_natCast_of_not_dvd`,
  `vp_natCast`, `vp_intCast`, `star_pow_dvd_iff`.
- `FormalGroupLaw.lean`: `omegaCoeff`, `omegaCoeff_eq`, `omegaCoeff_map`, `coeff_omega_rhs`,
  `chordSlope`, `omegaFst`.
- `FormalLogarithm.lean`: `evalLog_neg`, `evalLog_zero`, `zCoord_neg`,
  `logCoeffA_eq_zero_of_even`.

## Problems

- The formal group law (associativity, commutativity, `F(T,-T) = 0`), the evaluation identity
  `z(P+Q) = F(z(P), z(Q))`, `log ∘ F = log + log`, and `ellLog_add` are not proved. They are the
  real gap: Mathlib has the bare `FormalGroup` structure, but nothing on formal groups of
  elliptic curves, invariant differentials, or evaluation of two-variable series in a complete
  valued field.
- `omegaSeries_hasSum` is proved with the article's contraction argument. The series
  converges, and its sum `S` satisfies `S = z³ + A z S²` by a Cauchy product
  (`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`) and has `v(S) ≥ 3`; `w_eq_of_t_eq` then
  gives `S = -1/y`. This is the template for the evaluation part of `formalGroupLaw_exists`
  (step 2 of the plan below).
- Mathlib v4.35's `Valued` topology works through `v.restrict` and `ValueGroup₀`. The bridge
  lemmas in `Analytic.lean` hide this; reuse them rather than the raw API.
- `genCurve.toAffine.Point` and `(shortCurve (-genD^2)).toAffine.Point` are defeq but carry
  different `CommRing K0` instance paths. `rw` with `map_zsmul` fails across them, so state
  helpers in the `genCurve` type (see `mapE_zsmul`).

## Plan for the remaining sorries (suggestions for the next agent)

The downstream chapter only needs `ellLog_add`. Recommended route:

1. **The power-series identity `formalLog_formalAdd`, by differentiation.**
   - Work in `K⟦T₁,T₂⟧` (`MvPowerSeries (Fin 2) K`) and use `MvPowerSeries.pderiv 0`.
   - With `S = invDiffSeries A` and `F = formalAdd A`, prove the invariance of the differential:
     `S(F) · ∂₁F = S(T₁)`, where `S(F)` is `PowerSeries.subst F S`.
   - Since `S(T)(1 - 2A T ω(T)) = 1` (`invDiffSeries_mul`, using `X * uSeries A = omegaSeries A`),
     the invariance is equivalent to `∂₁F · (1 - 2A T₁ ω(T₁)) = 1 - 2A F ω(F)`.
   - This needs `ω(F) = -(ν + λ(-F))` up to the sign conventions (the third point lies on the
     chord) and the derivative of the chord formulas. Both are polynomial identities in
     `T₁, T₂, ω(T₁), ω(T₂), λ, ∂₁λ`, modulo the two relations `ωᵢ = Tᵢ³ + A Tᵢ ωᵢ²` and
     `λ(T₂ - T₁) = ω(T₂) - ω(T₁)`.
   - Clear the denominator `T₂ - T₁` by working in the fraction field of `K⟦T₁,T₂⟧`, which is a
     domain. Find the `linear_combination` coefficients with a computer-algebra system (sympy is
     available on the host).
   - Then `∂₁(log F - log T₁ - log T₂) = 0`. In characteristic 0 this makes it independent of
     `T₁`, and at `T₁ = 0` it is `0` because `F(0,T₂) = T₂`.
2. **Evaluation.**
   - For `P, Q ∈ W₁(K)`, `z(P+Q) = Σ F_n z(P)^{n₀} z(Q)^{n₁}`. The double sum converges by
     `summable_of_vK` over `Fin 2 →₀ ℕ` with the cofinite filter. Its value is the chord value
     (`chord_add`, Silverman's `-z₃`). This needs evaluation of `λ` at distinct points as the
     difference quotient, and the inverse `(1 + Aλ²)⁻¹`, through Cauchy products.
   - Alternatively, use Mathlib's `MvPowerSeries.eval₂` on `𝒪` with its `𝔪`-adic linear
     topology. It is a ring homomorphism on topologically nilpotent arguments, but an
     `IsLinearTopology 𝒪 𝒪` instance must be provided.
   - Finally, evaluate the identity of step 1 termwise. `log` has non-integral coefficients, but
     `v(b_{r-1} t^r / r) → ∞` uniformly on `v(t) ≥ 1` (see `vge_logTerm`).
3. **Associativity of `F`, needed only for `formalGroupLaw_exists`, not downstream.**
   - Silverman deduces it from the group law over `K⟦T₁,T₂,T₃⟧`. Here it can be obtained after
     step 1: `log` is invertible over `K` (`exp` exists formally in characteristic 0), and
     `log ∘ F = log + log` gives `F = exp(log T₁ + log T₂)`, which is associative and
     commutative.
   - Integrality of `F` holds by construction. `F(T,-T) = 0` follows from `log` being odd
     (`evalLog_neg`, at the series level `logCoeffA_eq_zero_of_even`).

So the cheapest path to `ellLog_add` is step 1 followed by step 2. Associativity then comes for
free from `exp`.

Other suggestions:

- To transfer `dyadic-generator` to `K_(s)`, use `mapE`-style maps (`Ratio.lean`) with
  `vComp_algebraMap`.
- `assembly/local-tests` and `size/formal-multiple` can relink to `formal_val_x_y`,
  `formalFilt`, `zCoord_injOn`, `zsmul_mem_W1` with `v = vP π hπ` (`K₀`) or `v = vComp π hπ`
  (completion).
