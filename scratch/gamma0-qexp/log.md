# gamma0-qexp log

Target: `ZInQ.GZAlg.Gamma0QExpansion` (ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic.lean:82), the frozenTarget
binder `hQ` of `ZInQ.OneProof.frozenTarget` (ZInQKernel/OneProof/Main.lean:94).

## 2026-11-16 17:30 setup
- origin/main merge: "Already up to date" (VERIFIED).
- Build tree copied (reflink) from the leaf-fold33b worktree (same commit 0e3c3125, Main.lean identical).
- Statement.lean: verbatim copies + rfl checks.

## Findings (reading)
- Consumer (VERIFIED, read): `grossZagierModuliOptAt_of_alg` applies hQ to the coordinates X, Y of the modular
  parametrization for every level N (quantified inside `GrossZagierModuliOptAt E`); these have poles in ℍ, so the
  general meromorphic statement for every N is needed; no narrowing helps.
- FLT vendored library (VERIFIED, read): level-one results need a Laurent expansion valid on all of ℍ
  (`mem_adjoin_jq_of_hasSum_of_slash_invariant`, `coeff_eq_zero_of_hasSum_of_slash_invariant`); no analytic
  ℂ(X₀(N)) = ℂ(j, j_N) statement, no meromorphic level-one statement, no analytic distinctness of the j(Nγτ).
  Useful: `hasSum_jq_qParam` (all τ), `hasSum_qParam_mul_laurent`, `laurent_qParam_coeff_unique`, `qTwist`,
  `coeffEmb`, and the public `Realized.*` lemmas in the Sol of coeff_eq_zero (mdifferentiable, coeff_unique).
- Mathlib 4.35 (VERIFIED, read): `hasSum_qExpansion` (periodic + MDifferentiable + bounded at ∞ ⇒ q-expansion on
  all ℍ), `ModularGroup.exists_smul_mem_fd`, `MeromorphicOn.analyticAt_mem_codiscreteWithin`,
  `IsCompact.finite_sdiff_of_mem_codiscreteWithin`, `MeromorphicAt.comp_analyticAt`,
  `Complex.differentiableOn_update_limUnder_of_bddAbove`, `instFiniteIndexGamma0`.

## Plan (classical proof, all glue)
1. Level one, holomorphic (L1H): F analytic on ℍ, SL₂(ℤ)-invariant, |F| ≤ C e^{2πk Im τ} ⇒ F = P(j), P ∈ ℂ[X].
2. Level one, meromorphic (L1M): pole clearing with finitely many poles in the truncated fundamental domain.
3. Symmetrization over Γ₀(N)\SL₂(ℤ): R(Y) = Σ_c g_c ∏_{c'≠c}(Y − J_{c'}), S(Y) = Σ_c ∏_{c'≠c}(Y − J_{c'}),
   J_c(τ) = j(Nγ_c⁻¹τ); g·S(j_N) = R(j_N); coefficients are level-one functions.
4. Distinctness: |j(Nτ)| ≈ e^{2πN Im τ} beats |J_c| ≤ C e^{2π(N/4) Im τ} for c ≠ Γ₀(N) (Bezout form of Nγ).
5. Bridge: identity B(j,j_N)g = A(j,j_N) codiscretely ⇒ Laurent identity in ℂ((q)) (shift τ ↦ τ + iT', qTwist).
6. Descent: ℚ-linear functional ℂ → ℚ ⇒ x ∈ ℚ(jq, jqN).

## 2026-11-16 17:35-18:02 proofs (all VERIFIED: compiled with `lake env lean` / `lake build +module`)
Modules under ZInQKernel/Contrib/OneProof/ (new files only):
- Gamma0QExp/Descent.lean: `mem_of_complex_relation` (ℂ-relation B·x = A with B ≠ 0 over a subfield F ⊆ ℚ((q)) ⇒ x ∈ F).
- Gamma0QExp/QSeries.lean: `Rz` calculus (add/mul/C/aeval), `rz_jq`, `rz_jqN`, shifts (`shiftH`, `rUnit`, `rz_qTwist_of`),
  `continuousAt_of_rz`, `eq_zero_of_rz_shift` (vanishing criterion).
- Gamma0QExp/LevelOne.lean: `ModGrowth` calculus, `jf_bounds` (½e^{2πy} ≤ |j| ≤ 2e^{2πy}, y large), `jf_differentiableAt`,
  `levelOne_hol` (holomorphic SL₂(ℤ)-invariant + moderate growth ⇒ polynomial in j).
- Gamma0QExp/LevelOneMero.lean: `EvNe`, `levelOne_mero` (meromorphic invariant + moderate growth ⇒ B(j)F = A(j) off a
  discrete set, B ≠ 0), by pole clearing on the truncated fundamental domain + removable singularities.
- Gamma0QExp/Reduce.lean: `jN_smul_of_mem` (j(N h w) = j(N w), h ∈ Γ₀(N)), `exists_reduce` (Bézout: j(Nδw) = j((aw+b)/d),
  ad = N, a < N if δ ∉ Γ₀(N)), `jN_smul_bound`, `jN_lower`, `jN_separation`, `modGrowth_jN_smul`.
- Gamma0QExp/Cosets.lean: `symPoly`, cosets `Cos N = SL₂(ℤ)/Γ₀(N)`, `conjF`, `conjJ`, `coeff_levelOne`, `analytic_core`.
- Gamma0QExpansion.lean: `ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof : ZInQ.GZAlg.Gamma0QExpansion`.
- `#print axioms gamma0QExpansion_proof`: [propext, Classical.choice, Quot.sound] (scratch/gamma0-qexp/Axioms.lean).
- No new leaf, no new glue Prop: the statement is proved for every N ≥ 1 exactly as stated.
