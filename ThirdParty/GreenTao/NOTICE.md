# Vendored Green–Tao proof: notice

## Source

- Repository: Vilin97/Autoformalization (https://github.com/Vilin97/Autoformalization), directory `green-tao/`.
- Commit: `0dc67d87416c19690dd641a178ada32cca95c651` ("prove Green-Tao via source-full removal", 2026-07-31).
- Files copied: `ChallengeDeps.lean`, `Submission.lean` and the whole `Submission/` directory (229 modules,
  all reachable from `Submission.lean`), plus the repository's `LICENSE` (copied here as `LICENSE`).
  Module names (`ChallengeDeps`, `Submission.*`) and namespaces are unchanged. The `Challenge.lean`/
  `Solution.lean` benchmark wrappers and the `blueprint/` directory of the source are not copied.
- Upstream toolchain: Lean v4.32.2, Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`.

## License

Apache License, Version 2.0; see `LICENSE` in this directory. The modifications listed below are
distributed under the same license.

## Authors and attribution

The proof was produced with GPT-5.6 Sol in Codex under the direction of Vasily Ilin, as a submission
(recorded in the lean-eval submission record) to the `green_tao` target of the lean-eval benchmark
(leanprover/lean-eval, commit `43fc8cf16396a3b0f789fe5bea65837e866aba15`). The trusted statement is
`ChallengeDeps.lean` (definition `LeanEval.NumberTheory.ContainsArbitraryAPs`) together with the
benchmark's `theorem green_tao : ContainsArbitraryAPs {p : ℕ | Nat.Prime p}` (Green–Tao 2008,
Theorem 1.1), proved here as `Submission.green_tao`.

## Modifications in this repository

In the fork Deicyde/diophantine-z-q the files were first committed unchanged, then ported to Lean
4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` with local proof edits only. No statement was changed,
and no `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern` or kernel-skipping option
was added (the source contains none either). `#print axioms Submission.green_tao` reports
`propext`, `Classical.choice`, `Quot.sound`.

Each modified file starts with a one-line comment saying that it was changed in this repository
(Apache License 2.0, section 4(b)); the counts below do not include those lines.

Kinds of change:

1. Mathlib renamed the ordered-semiring product lemmas to `₀` forms: `Finset.prod_le_prod` →
   `Finset.prod_le_prod₀` (46 sites), `Finset.prod_le_one` → `Finset.prod_le_one₀` (21),
   `Finset.prod_le_prod_of_subset_of_one_le` → `…₀` (2), `Finset.prod_le_prod_of_subset_of_le_one` → `…₀` (2).
2. `convert … using 1` (and `simp`) now close definitional side goals themselves: trailing `rfl`,
   `· rfl` or `· congr 1` steps that failed with "No goals" were removed (about 16 sites); conversely one
   site needed an added `rfl`.
3. Changed simp normal forms: a few `simp`/`simpa` calls replaced by `convert … <;> rfl`, `subst`+`exact`,
   `rw`+`exact`, or a direct `exact` of the lemma (Sieve/LocalFactors, Sieve/PrimeHarmonicProductBound,
   Sieve/WTrickedEulerCorrection, Transference/BooleanCutReduction, Transference/ConvolutionClosure).
4. One `rw` with an iff lemma (`summable_prod_of_nonneg`) failed with a motive error and became
   `refine (…).2 ?_` (Sieve/CFZCanonicalEulerCompletion).

The detailed per-change log is in `scratch/gt-import/log.md` at the repository root. Comparing each
file with `green-tao/` at the source commit above shows every edit.

Modified files (paths relative to this directory):

- `Submission/ArithmeticProgression/Count.lean`
- `Submission/Hypergraph/AdaptiveCoarseTargetRegularity.lean`
- `Submission/Hypergraph/AdaptiveRegularityParameterSchedule.lean`
- `Submission/Hypergraph/BundleCountingRecurrence.lean`
- `Submission/Hypergraph/CoarseConfigurationCounting.lean`
- `Submission/Hypergraph/CoarseTargetRegularity.lean`
- `Submission/Hypergraph/ConfigurationWeightedHierarchy.lean`
- `Submission/Hypergraph/GrowthFunctionComplexRegularity.lean`
- `Submission/Hypergraph/HypergraphBundleCounting.lean`
- `Submission/Hypergraph/HypergraphBundleFrozenCut.lean`
- `Submission/Hypergraph/HypergraphBundleGeneralizedCounting.lean`
- `Submission/Hypergraph/HypergraphBundleRelativeCounting.lean`
- `Submission/Hypergraph/LookaheadGeneratedCellRemoval.lean`
- `Submission/Hypergraph/OrderedBoundaryPartition.lean`
- `Submission/Hypergraph/OrderedCellLifting.lean`
- `Submission/Hypergraph/OrderedConfigurationCounting.lean`
- `Submission/Hypergraph/OrderedCounting.lean`
- `Submission/Hypergraph/OrderedEnergy.lean`
- `Submission/Hypergraph/OrderedFullBoundary.lean`
- `Submission/Hypergraph/OrderedRegularizedCells.lean`
- `Submission/Hypergraph/OrderedStrongCleaning.lean`
- `Submission/Hypergraph/RankwiseStageShiftedRegularity.lean`
- `Submission/Hypergraph/RegularizedCells.lean`
- `Submission/Hypergraph/Simplex.lean`
- `Submission/Hypergraph/SourceFullBundleRemovalAssembly.lean`
- `Submission/Hypergraph/SourceFullCoarseTargetRegularity.lean`
- `Submission/Hypergraph/SourceFullRankwiseBundleCounting.lean`
- `Submission/Hypergraph/StrongOrderedComplexRegularity.lean`
- `Submission/Hypergraph/StructuredCleaning.lean`
- `Submission/Hypergraph/SuffixConfigurationCounting.lean`
- `Submission/Sieve/CFZCanonicalCarryEulerBridge.lean`
- `Submission/Sieve/CFZCanonicalDivisorRankinMassPolylog.lean`
- `Submission/Sieve/CFZCanonicalDivisorRankinTruncation.lean`
- `Submission/Sieve/CFZCanonicalDivisorTruncation.lean`
- `Submission/Sieve/CFZCanonicalEulerCompletion.lean`
- `Submission/Sieve/CFZCanonicalEulerCompletionTail.lean`
- `Submission/Sieve/CFZCarryBlockEulerBridge.lean`
- `Submission/Sieve/CFZCarryFourierTailBound.lean`
- `Submission/Sieve/CFZCongruenceBoundary.lean`
- `Submission/Sieve/ComplexLocalFactorControl.lean`
- `Submission/Sieve/ComplexZetaModelComparison.lean`
- `Submission/Sieve/DivisorCoefficientBounds.lean`
- `Submission/Sieve/LocalFactors.lean`
- `Submission/Sieve/PrimeHarmonicProductBound.lean`
- `Submission/Sieve/WTrickedEulerCorrection.lean`
- `Submission/Sieve/WTrickedGoodPrime.lean`
- `Submission/Transference/BooleanCutReduction.lean`
- `Submission/Transference/BoxNorm.lean`
- `Submission/Transference/ConvolutionClosure.lean`
- `Submission/Transference/Densification.lean`
- `Submission/Transference/GeneralRelativeSimplexStep.lean`
- `Submission/Transference/GeneralizedConvolution.lean`
- `Submission/Transference/RelativeCountingCertificate.lean`
- `Submission/Transference/RelativeCountingDecoderStep.lean`
- `Submission/Transference/RelativeCountingHeterogeneousMask.lean`
- `Submission/Transference/RelativeCountingInduction.lean`
- `Submission/Transference/RelativeDensification.lean`
- `Submission/Transference/RelativeSimplexIteration.lean`
- `Submission/Transference/SimplexCounting.lean`
