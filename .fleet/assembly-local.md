# assembly-local: the six local tests at finite places

All eight leaves are formalized and proved: no `sorry`, no new axiom, no `native_decide`.
`#print axioms` on the main theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
The modules are under `ZInQKernel/Assembly/Local/`. The root module is
`ZInQKernel/Assembly/Local.lean`, imported from `ZInQKernel.lean`. `lake build ZInQKernel` passes.

The branch merges `origin/wip/size-formal` for the reduction orders of `P₀`
(`ZInQ.Size.exists_reduction_multiple`). That branch had no `sorry` when merged.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| multiplication/local/chord-estimate.md | `ZInQ.Mult.chord_add_five` (in `Multiplication/Local/Chord.lean`), with `ZInQ.Mult.formal_third_point_five` | proved |
| assembly/local-tests/formal-multiplication.md | `ZInQ.Assembly.val_zCoord_add_sub` (item 1), `val_zCoord_zsmul_sub` (item 2), `zsmul_mem_formalFilt_succ`, `zsmul_mem_formalFilt_add_val`, `val_intCast_eq` (item 3), `zCoord_zsmul_eq_mul_unit` (item 4); on `K₀`: `Ek`, `zCoord_zsmul_eq_mul_unit_K0`, `zsmul_mem_Ek_of_dvd`, `zsmul_mem_Ek_sqrt2`, `vP_natCast_self`, `vS_two_eq` | proved |
| assembly/local-tests/dyadic-trace.md | `ZInQ.Assembly.vS_star` (item 1; `vS_star'` for the additive valuation), `ZInQ.Assembly.vS_trace_ge` (item 2) | proved |
| assembly/local-tests/deep-multiples.md | `ZInQ.Assembly.exists_smul_mem_Ek`, `ZInQ.Assembly.exists_common_smul_mem_Ek` | proved |
| assembly/local-tests/pole-input-local.md | `ZInQ.Assembly.poleInput_local` | proved |
| assembly/local-tests/pole-input-real.md | `ZInQ.Assembly.poleInput_real` | proved |
| assembly/local-tests/test-divisibility.md | `ZInQ.Assembly.test_dvd` | proved |
| assembly/local-tests/test-completeness.md | `ZInQ.Assembly.test_complete` | proved |
| assembly/value-templates/six-local-tests.md (needed first, so defined here) | `ZInQ.Assembly.Test`, with `testD`, `testC`, `testR₀`, `testR`, `poleW`, `poleTheta`, `contactPoly`; the pole input `testB` | definition |

## How the statements differ from the articles

- **chord-estimate.** Stated in the coordinates of `chord_add`. The hypotheses are
  `v(x/y) ≥ m ≥ 1` and `v(1/y) ≥ 3m` for both points, with `P₁ + P₂ ≠ O`. The conclusion
  gives the sum as an affine point with the same bounds. It also gives `λ, ν` with `v(λ) ≥ 2m`
  and `v(ν) ≥ 3m`, the line `ω = λz + ν` through both points (the tangent when they are equal),
  the identity `z(P₁ + P₂) = z(P₁) + z(P₂) + 2Aλν/(1 + Aλ²)`, and
  `v(t₃ - t₁ - t₂) ≥ 5m`, where `t = x/y = -z`. The membership form for `P, Q ∈ W_k(K)`, which
  also covers `O`, is formal-multiplication item 1 (`val_zCoord_add_sub`). `chord_add` and
  `formal_third_point` keep their statements; they are now corollaries of the sharp lemmas.
- **formal-multiplication.**
  - The Lean statements work for any field with an additive valuation `K → ℤ ∪ {∞}`. They do
    not use characteristic 0, the normalization `v(K^×) = ℤ`, or the residue field. "Residue
    characteristic `p`" is expressed as `v(p) = e` plus `v(m) = 0` for every integer `m` with
    `p ∤ m`.
  - Item 3, second part: `[n]W_k ⊆ W_{k + e·v_p(n)}` when `v(p) = e ≤ 4`. This needs only
    `v(p) = e`. `val_intCast_eq` identifies `e·v_p(n)` with `v(n)` under the residue-characteristic
    hypothesis.
  - Item 4 needs only `v(p) = 1` and the residue-characteristic hypothesis; `p` odd is not used.
  - The `K₀` forms are proved at primes above odd `p` and, for item 3, at `(s)` with `e = 2`.
  - `ν_π(P)` has no separate definition. It is `vP π hπ (zCoord P)`.
- **dyadic-trace.** Stated with the model chapter's `vp` (value `0` at `0`), so item 2 reads
  `Tr x = 0 ∨ k + 1 ≤ v₂(Tr x)`, the same shape as `ZInQ.Mult.vp_trace_ge`.
- **deep-multiples.** `N : ℤ` with `1 ≤ N`. The finite-set version takes any `Ps : Finset Zs`
  and quantifies over `π ∈ Ps` with a primality proof. `Ek_congr` shows that `E_k(π)` depends
  only on the associate class of `π`.
- **pole-input-local.**
  - The article takes `η` with the sign of `F(n)`. The Lean statement assumes only `η² = 1`,
    because the local conditions do not depend on the sign.
  - "Prime elements dividing `R₀`" is stated as primes `π ∣ 2730⁶·F(n)` in `ℤ[s]`, which have
    the same divisors because `η = ±1`. The same applies to "`v_p(q) ≥ 0` for `p ∣ R₀`".
  - The hypothesis is `∃ N, 1 ≤ N ∧ v_π(F(n)) ≤ N ∧ [κ]P₀ ∈ E_N(π)`.
  - The conclusion is `4 ≤ v₂(B)`, `6 ≤ v_p(B)` for `p ∈ {3, 5, 7, 13}`, and
    `IsSquare B.den`, with `B = testB n κ n η q (2κ) (2κn)`.
- **pole-input-real.** As in the article: `R₀ : ℕ`, `1 < R₀`, `C : Fin 6 → K₀`, and the
  conclusion `Nat.Coprime q.den R₀`, `a₀ ≠ 0`, `W ≠ 0`, `Θ ≠ 0`, `0 < R/Θ² < 1/2`. The
  article's remark that "adjusting by one" is never needed is confirmed: `a₀ ≠ 0` is proved
  directly.
- **test-divisibility.** `test_dvd : Test n κ t → contactSupport heightPrimes t ∣ (κ * sixF n).natAbs`.
  No hypothesis is used.
- **test-completeness.**
  `test_complete (hPC : PoleCompleteness) (n : ℤ) (hn : (n : ℚ) ∉ contactSet) : ∃ κ ≠ 0, Test n κ n`.
  Instead of "one prime per associate class", the primes are `UniqueFactorizationMonoid.factors`
  of `R₀`. `N = 1 + Σ_π v_π(F(n))` replaces `1 + max`.
- **six-local-tests (definition).** `Test n κ t` is `κ ≠ 0 ∧ t ∉ contactSet ∧ ∃ h s₀ η q, …`.
  The six tests use `ZInQ.Mult.zCoord`/`wCoord` with `A := -genD ^ 2`, `star` for `σ`, and
  `Θ = QuadraticAlgebra.trace W⁻¹`. The pole condition is
  `PoleSoluble (testR η q t / poleTheta … ^ 2)`, which is `testB` by `rfl`.

## Lemmas added beyond the leaves

- **The one-sided pole obstruction** (`multiplication/pole-obstruction.md`, Lemma 5.1):
  `ZInQ.Assembly.poleSoluble_no_negative_odd`, through `poleSystem_of_polePoly`, which
  reduces `ZInQ.PoleSoluble` to upstream's `ZInQ.ValuationObstruction.poleSystem`. It uses
  upstream's `poleSystem_no_negative_odd_valuation` (`lean/ZInQ/PoleValuation.lean`). That
  article has no `lean:` field yet, so this declaration can fill it.
- **Generic multiplication facts:** `zCoord_neg`, `val_zCoord_nsmul_sub`,
  `zsmul_mem_formalFilt_of_vge` (`[n]W_k ⊆ W_{k + min(e, 4k)}` when `v(n) ≥ e`),
  `zCoord_zsmul_eq_mul_unit_of_val`, `zCoord_zsmul_ratio` / `zCoord_zsmul_ratio_K0`
  (`z([b]Q)/z([a]Q) = (b/a)·w`, `w ≡ 1`).
- **Lemma 11.1 pieces:** `contact_val` (`v_p(F(t)) = v_p(t - c)`), `contactSet_int`,
  `testR_val`, `vp_poleW_factor`, `tests_small`, `trace_val`, `pole_step`,
  `mem_Ek_one_of_wCoord`, `ratio_congr`, `prime_dvd_of_test`.
- **Valuation helpers:** `vP_ratCast`, `vge_ratCast_iff`, `dvd_of_vge_intCast`, `vP_star`,
  `vge_star_iff`, `exists_prime_dvd_natCast`, `exists_prime_below`, `vp_prod`, `vP_congr`,
  `Ek_congr`, `vge_natCast_of_dvd`, `natCast_dvd_of_dvd`, `vge_zero_ratCast`.
- **Rational facts:** `den_val` (`v_p(den B) = max(0, -v_p(B))`) and `isSquare_den_of`.
- **Lemma 11.2 pieces:** `tests_deep`, `inv_poleW_close`, `padicValRat_2730`, `exists_q_small`,
  `poleW_small`, `padicValRat_nonneg_of_coprime`.

## Problems

- `ZInQ.Assembly.Test` and its helpers are defined here because the assembly-values task has
  not started. That task should import `ZInQKernel.Assembly.Local.SixLocalTests` rather than
  redefine them, or the two definitions will clash once both are imported from
  `ZInQKernel.lean`.
- There are now three copies of the local parameter `z`: `ZInQ.Mult.zCoord` (used here),
  `ZInQ.Assembly.zCoord` (real places) and `ZInQ.Compiler.Precision.zPt`. All are `-x/y`
  defined by matching on the point, so they agree by cases on the point. A bridging lemma will
  be needed when the value-test semantics connects `Test` to the templates.
- `genCurve` and `shortCurve (-genD ^ 2)` points carry different instance paths. The lemmas
  here are stated for `genCurve.toAffine.Point` (`Ek`, `genP0`, `m • genP0`) and apply the
  generic lemmas with `exact`. `rw` across the two fails, as expected.

## Suggestions for the next agent

- assembly-values: build the value-test semantics on `Test`, `test_dvd` and `test_complete`.
  `test_dvd` plus `sixContact_at_heightPrimes` with `A0_eq_heightH6` gives
  `h(t) ≤ bound n κ` directly, because `bound n κ = A0 · |κ F(n)|²⁴`.
- Blueprint `lean:` fields:
  - chord-estimate: `ZInQ.Mult.chord_add_five`.
  - formal-multiplication: `ZInQ.Assembly.val_zCoord_add_sub`, `val_zCoord_zsmul_sub`,
    `zsmul_mem_formalFilt_succ`, `zsmul_mem_formalFilt_add_val`, `zCoord_zsmul_eq_mul_unit`,
    `Ek`.
  - dyadic-trace: `ZInQ.Assembly.vS_star`, `vS_trace_ge`.
  - deep-multiples: `ZInQ.Assembly.exists_smul_mem_Ek`, `exists_common_smul_mem_Ek`.
  - pole-input-local: `ZInQ.Assembly.poleInput_local`.
  - pole-input-real: `ZInQ.Assembly.poleInput_real`.
  - test-divisibility: `ZInQ.Assembly.test_dvd`.
  - test-completeness: `ZInQ.Assembly.test_complete`.
  - six-local-tests: `ZInQ.Assembly.Test`.
  - pole-obstruction: `ZInQ.Assembly.poleSoluble_no_negative_odd`.
- The assembly implementation notes should be updated to the exported names above.
