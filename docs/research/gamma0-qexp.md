# gamma0-qexp: the `q`-expansion principle for `Γ₀(N)` is proved

## 1. Result

**`ZInQ.GZAlg.Gamma0QExpansion` is proved in Lean for every level `N ≥ 1`, exactly as stated, with no new
hypotheses and only the standard axioms** (VERIFIED: compiled, `#print axioms`, `#discharges`):

```lean
theorem ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof : ZInQ.GZAlg.Gamma0QExpansion
```

in `ZInQKernel/Contrib/OneProof/Gamma0QExpansion.lean`. It imports `ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic`
(the module that declares the statement) and the helper modules `ZInQKernel/Contrib/OneProof/Gamma0QExp/*.lean`.
It does not import `ZInQKernel.OneProof.Main`.

So the frozenTarget binder `hQ` (OPEN.md row `hQ`, LEAF, unverified locator) is closed. **hQ leaves
`frozenTarget`: −1, no new leaf, no new glue Prop.** It is a manual fold, because `hQ` is a binder of
`frozenTarget` and autofold cannot handle that. The fold is `scratch/gamma0-qexp/FoldCheck.lean`, which proves
`ZInQ.FrozenTarget` without `hQ` (section 4).

The statement (`GrossZagierAlgebraic.lean:82`): if `g : ℍ → ℂ` satisfies `ZInQ.GZHeegner.IsRatModFnMero N g`
(Γ₀(N)-invariant, meromorphic on `ℍ`, `g(γτ) = O(e^{2πk Im τ})` at every cusp, and a rational `q`-expansion near
`∞`) and `x ∈ ℚ((q))` with `HasQExp g x`, then `x ∈ X0Field N = ℚ(jq, jq(q^N))` (FLT's `modularFunctionField N`).
Statement checks (VERIFIED, by reading and by the proof):
* The statement is true, and it is not vacuous. The consumer `grossZagierModuliOptAt_of_alg` applies it to the
  coordinates of the modular parametrization at every level. These have poles in `ℍ`, so the meromorphic,
  all-`N` form is needed, and that form is what is proved.
* The proof uses three clauses of `IsRatModFnMero`: invariance, meromorphy, and moderate growth at every cusp.
  The fourth clause (the ℕ-indexed rational expansion) is not used. Rationality enters only through
  `x ∈ ℚ((q))` and `HasQExp`.

## 2. Proof (all glue, proved in Lean)

This is the classical argument (Shimura 1971 §6.2–6.9; Diamond–Shurman §7.5–7.7; locators UNVERIFIED, no copy on
this host). Each step is a Lean theorem in a helper module.

| step | Lean | content |
|---|---|---|
| level one, holomorphic | `LevelOne.lean: levelOne_hol` | Let `G` be holomorphic and SL₂(ℤ)-invariant with `G = O(e^{2πk Im τ})`. Then `G = P(j)` with `P ∈ ℂ[X]`. Proof: `q^k G` is periodic, holomorphic and bounded at `∞`, so it has a `q`-expansion on all of `ℍ` (Mathlib `hasSum_qExpansion`). Subtract a polynomial in `j` to kill the principal part (induction with FLT's `coeff_jq_pow_self`). The remainder is constant (FLT's `coeff_eq_zero_of_hasSum_of_slash_invariant`). |
| level one, meromorphic | `LevelOneMero.lean: levelOne_mero` | Let `F` be meromorphic and invariant, with moderate growth. Then `B(j)F = A(j)` on punctured neighbourhoods of every point, with `B ≠ 0`. Proof by pole clearing. The non-analytic points of `F` in the compact set `{|Re z| ≤ ½, ½ ≤ Im z ≤ T₀}` are finite (`IsCompact.finite_sdiff_of_mem_codiscreteWithin`), and `F` is bounded above `T₀`. With `Q = ∏(X − j(z))^M`, `Q(j)F` is locally bounded on `ℍ` (move points into `ModularGroup.fd`; at a pole, `j − j(z) = O(τ − z)`). By Riemann's removable singularity theorem, `Q(j)F` agrees off a discrete set with a holomorphic invariant function of moderate growth, and `levelOne_hol` applies to that function. |
| `j` | `LevelOne.lean` | `jf_smul` (FLT `E4_cube_div_discriminant_smul`); `jf_differentiableAt`; `jf_bounds`: `½e^{2π Im τ} ≤ ‖j(τ)‖ ≤ 2e^{2π Im τ}` for large `Im τ` (from `q·j → 1`, FLT's `hasSum_jNum_qParam`). |
| `j(N·)` | `Reduce.lean` | `jN_smul_of_mem`: `j(N h w) = j(N w)` for `h ∈ Γ₀(N)`. `exists_reduce` (Bézout): `j(Nδw) = j((aw+b)/d)` with `ad = N`, and `a < N` when `δ ∉ Γ₀(N)`. `jN_smul_bound` and `jN_lower` give `jN_separation`: `j(Nδw) ≠ j(Nw)` for `δ ∉ Γ₀(N)` and large `Im w`. |
| symmetrization | `Cosets.lean: coeff_levelOne, analytic_core` | Work over the cosets `c ∈ SL₂(ℤ)/Γ₀(N)` with `g_c = g∘γ_c⁻¹` and `J_c = j_N∘γ_c⁻¹`. Each coefficient of `R(Y) = Σ_c g_c ∏_{c'≠c}(Y − J_{c'})` and `S(Y) = Σ_c ∏_{c'≠c}(Y − J_{c'})` is a universal polynomial in meromorphic functions of moderate growth, and is SL₂(ℤ)-invariant (the cosets are permuted), so it is rational in `j`. At `Y = j_N` we get `g·S(j_N) = R(j_N)`, with `S(j_N) = ∏_{c≠1}(j_N − J_c) ≠ 0` for large `Im τ`. Output: `B(j, j_N)·g = A(j, j_N)` off a discrete set, with `A, B ∈ ℂ[X,Y]` and `B(j, j_N)` not identically zero. |
| bridge | `QSeries.lean: eq_zero_of_rz_shift` | The identity carries over to `q`-expansions in `ℂ((q))`. Shift `τ ↦ τ + it` (FLT's `qTwist`) so that every series converges on all of `ℍ`. A `q`-series sum is continuous (FLT's `Realized.mdifferentiable`), so the sum vanishes everywhere, and its coefficients vanish by uniqueness (FLT's `laurent_qParam_coeff_unique`). |
| descent | `Descent.lean: mem_of_complex_relation` | Start from `B·x = A` in `ℂ((q))`, where `B ≠ 0` and `A` are `ℂ`-combinations of elements of a subfield `F ⊆ ℚ((q))`. Apply a `ℚ`-linear functional `λ: ℂ → ℚ` with `λ(B_m) ≠ 0` to the coefficients. The result is a relation over `ℚ`, so `x ∈ F`. |
| assembly | `Gamma0QExpansion.lean: gamma0QExpansion_proof` | Steps above, with `F = ℚ(jq, jqN)` (`jq_mem`, `jqN_mem`). |

Libraries used (VERIFIED, by reading): Mathlib 4.35 (`hasSum_qExpansion`, `ModularGroup.exists_smul_mem_fd`,
`MeromorphicOn.analyticAt_mem_codiscreteWithin`, `MeromorphicAt.comp_analyticAt`,
`Complex.differentiableOn_update_limUnder_of_bddAbove`, `CongruenceSubgroup.instFiniteIndexGamma0`), and the vendored
FLT modular-curve library (`hasSum_jq_qParam`, `hasSum_jNum_qParam`, `hasSum_qParam_mul_laurent`,
`laurent_qParam_coeff_unique`, `coeff_eq_zero_of_hasSum_of_slash_invariant`, `qTwist`, `coeffEmb`, and the public
`Realized.*` lemmas in the solution file of `coeff_eq_zero_of_hasSum_of_slash_invariant`). Nothing new from FLT was
vendored.

## 3. Files

* `ZInQKernel/Contrib/OneProof/Gamma0QExpansion.lean` (the final theorem, 5 KB).
* `ZInQKernel/Contrib/OneProof/Gamma0QExp/{Descent,QSeries,LevelOne,LevelOneMero,Reduce,Cosets}.lean`
  (helpers, 4–18 KB each, 87 KB in total). There is no `sorry`, no `axiom`, and no code that runs at build time
  (no `#eval`/`#print`/notation/macros; the `local notation` for `𝕢` was removed).
* `scratch/gamma0-qexp/`: `Statement.lean` (verbatim copies of the Prop and its dependencies, with `rfl` checks
  against the originals), `Axioms.lean`/`axioms.out`, `DischargesCheck.lean`/`discharges.out`,
  `FoldCheck.lean`/`foldcheck.out`, and `log.md`.

## 4. Checks (VERIFIED, 2026-11-16, this worktree on 0e3c3125)

* `lake build +ZInQKernel.Contrib.OneProof.Gamma0QExpansion`: success.
* `#print axioms ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof`: `[propext, Classical.choice, Quot.sound]`.
* `#discharges` (`scratch/gamma0-qexp/DischargesCheck.lean`, the kit's recipe):
  ```
  DISCHARGES [hQ] by ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
    still assumes: []
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 43 open hypotheses, 8721 theorems checked, 49 discharge one
  ```
* Manual fold (`scratch/gamma0-qexp/FoldCheck.lean`): `ZInQ.OneProof.frozenTarget_noQ` has Main's binders
  without `hQ`, and its body is Main's with `hQ := gamma0QExpansion_proof`. Axioms: `[propext, Classical.choice,
  Quot.sound]`. An `example` checks that it is `frozenTarget … gamma0QExpansion_proof …`.

## 5. Integration

The fold of `ZInQKernel/OneProof/Main.lean` is not done in the tree, because this task edits nothing else under
`ZInQKernel/`. Three changes are needed:
1. add `import ZInQKernel.Contrib.OneProof.Gamma0QExpansion`;
2. delete the binder `(hQ : ZInQ.GZAlg.Gamma0QExpansion)`;
3. replace `hQ` by `ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof` in
   `ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ hQ hW`, as in `FoldCheck.lean`.

OPEN.md row `hQ` (and issue elliotglazer #76) can be closed. No new locator row is needed, because no leaf was
added.
