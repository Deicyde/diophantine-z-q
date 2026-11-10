# gt-import log

## Step 1 (copy)
- Source: ~/gt-src/Autoformalization at 0dc67d87416c19690dd641a178ada32cca95c651, green-tao/.
- Copied ChallengeDeps.lean, Submission.lean, Submission/ (229 modules) and LICENSE to ThirdParty/GreenTao/ unchanged.
- All 229 Submission/ modules are reachable from Submission.lean; lean_lib GreenTaoVendor with roots Submission, ChallengeDeps
  and leanOptions autoImplicit = false (as in the source lakefile).

## Step 2 (port), batch 1
Build outputs kept in scratch/gt-import/build*.txt.
- Order lemmas renamed (Mathlib now has `₀` versions for ordered semirings; unsubscripted names are for ordered
  comm monoids): Finset.prod_le_prod → prod_le_prod₀ (46 sites), prod_le_one → prod_le_one₀ (21),
  prod_le_prod_of_subset_of_one_le → …₀ (2), prod_le_prod_of_subset_of_le_one → …₀ (2).
  Files: ArithmeticProgression/Count, Hypergraph/{AdaptiveRegularityParameterSchedule, BundleCountingRecurrence,
  CoarseConfigurationCounting, HypergraphBundle*, LookaheadGeneratedCellRemoval, Ordered*, RankwiseStageShiftedRegularity,
  RegularizedCells, Simplex, SourceFull*, StructuredCleaning, SuffixConfigurationCounting}, Sieve/*, Transference/*
  (see `git show` of this commit).
- simp/simpa normal-form changes (simp now closes differently or loops/does nothing):
  Sieve/LocalFactors (2× `simpa using h` → `convert h <;> rfl`), Sieve/PrimeHarmonicProductBound
  (`simpa [← hq]` → `subst hq; exact`), Sieve/WTrickedEulerCorrection (simp → rw + exact Finset.prod_attach),
  Transference/BooleanCutReduction (simpa [defs] using t → exact t).
