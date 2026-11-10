# gt-import report

| article path | Lean name | status |
| --- | --- | --- |
| (task: vendor Green–Tao) ThirdParty/GreenTao/Submission.lean | `Submission.green_tao` | proved (ported, builds) |
| ZInQKernel/External/GreenTaoPrimes.lean | `ZInQ.greenTao_primes : ZInQ.ContainsArbitraryAPs {p : ℕ \| p.Prime}` | proved |

## What was copied
From Vilin97/Autoformalization, `green-tao/` at `0dc67d87416c19690dd641a178ada32cca95c651` (Apache-2.0):
`ChallengeDeps.lean`, `Submission.lean`, all of `Submission/` (229 modules) and `LICENSE`, into
`ThirdParty/GreenTao/`, module names and namespaces unchanged. Unmodified copy is commit ec43491.
lakefile.toml: `[[lean_lib]] GreenTaoVendor`, srcDir `ThirdParty/GreenTao`, roots `Submission`, `ChallengeDeps`,
`autoImplicit = false` (as upstream). Provenance: `ThirdParty/GreenTao/NOTICE.md`; entry added to `THIRD_PARTY_NOTICES.md`.

## Porting changes (Lean 4.32.2 / Mathlib 905b958 → Lean 4.35.0 / Mathlib v4.35.0)
59 files changed, 89 insertions, 105 deletions; no statement changed.
1. `₀` renames of ordered-semiring product lemmas: `Finset.prod_le_prod₀` 46, `Finset.prod_le_one₀` 21,
   `prod_le_prod_of_subset_of_one_le₀` 2, `prod_le_prod_of_subset_of_le_one₀` 2 (71 sites).
2. `convert … using 1` / `simp` now close defeq side goals: ~16 trailing `rfl` / `· rfl` / `· congr 1` removed
   (CoarseTargetRegularity, StrongOrderedComplexRegularity, CFZCanonicalEulerCompletion, OrderedCellLifting,
   AdaptiveCoarseTargetRegularity, GrowthFunctionComplexRegularity, SourceFullCoarseTargetRegularity); 2 `rfl` added
   (RelativeCountingDecoderStep and one more).
3. simp normal-form changes, 6 sites: `simpa` → `convert h <;> rfl` (LocalFactors ×2), `subst; exact`
   (PrimeHarmonicProductBound), `rw; exact Finset.prod_attach` (WTrickedEulerCorrection), `exact` (BooleanCutReduction),
   `exact mean_const` (ConvolutionClosure.eval_pure).
4. `rw` with an iff → `refine (summable_prod_of_nonneg …).2 ?_` (CFZCanonicalEulerCompletion), 1 site.
Full file list in NOTICE.md; per-batch log in scratch/gt-import/log.md.
Deprecation warnings (e.g. `div_pos_iff`-style renames) remain as warnings only; they do not affect the build.

## Checks
- `lake build GreenTaoVendor`: success (9278 jobs). The vendored code has no `sorry`, `axiom`, `native_decide`,
  `implemented_by`, `extern` or `set_option` at all.
- `#print axioms Submission.green_tao` and `#print axioms ZInQ.greenTao_primes`: `[propext, Classical.choice, Quot.sound]`.
- `lake build ZInQKernel`: success (9841 jobs).
- Build time: the sum of per-module elaboration times of the 230 vendored modules is about 950 s (≈16 min
  sequential); with lake's parallelism the vendored library builds in a few minutes of wall time. No module
  exceeds 17 s. Slowest: Hypergraph.SourceFullCoarseTargetRegularity 17 s, Sieve.TruncatedDivisorSum 16 s,
  Sieve.CongruenceAverage 16 s, Finite.Mean 16 s, Sieve.ZetaNearOne 15 s, Sieve.SmoothCutoff 13 s,
  Primes.Chebyshev 12 s, Hypergraph.OrderedCellLifting 10 s, GreenTao.Parameters 10 s.
  (Times collected from the incremental build logs; a timed clean rebuild was not run, to avoid deleting build output.)

## Statement corrections
None. `ZInQ.ContainsArbitraryAPs` and `LeanEval.NumberTheory.ContainsArbitraryAPs` have identical bodies, so the
bridge is the term `Submission.green_tao`.

## Lemmas added beyond the task
None.

## Problems
None outstanding; everything ported.

## Suggestions for the next agent
- `ZInQ.greenTao_primes` is Theorem 1.1 of Green–Tao (all primes). The project's `GreenTaoDense` hypothesis
  (Hypotheses/GreenTao.lean) is the *relative-density* form (Theorem 1.2 / Szemerédi in the primes), which this
  vendored theorem does not give directly. The vendored proof goes through transference
  (`GreenTao.containsArbitraryAPs_primes_of_orderedRemoval_of_linearForms`); it may be adaptable to dense subsets of
  the primes, since the relative Szemerédi argument applies to any subset of positive relative density — worth
  inspecting `Submission/GreenTao/*` and `Submission/Transference/*` for where the full prime set is used.
- Fix the remaining deprecation warnings if the vendor tree is ever re-synced with a newer Mathlib.
