# gt-dense-plan report

Plan: `docs/research/gt-dense.md`. Log: `scratch/gt-dense-plan/log.md`.

## Summary

- The Ilin proof of Green–Tao Theorem 1.1 (commit `0dc67d8`) touches the set of primes in only three
  places:
  - the weight `wTrickedPrimeWeight` (`Submission/Primes/WTrick.lean:46`);
  - the Chebyshev density pigeonhole (`Submission/Primes/WTrickDensity.lean`, `Submission/Primes/Chebyshev.lean`);
  - the two ends of the proof: extraction (`Submission/Primes/Extraction.lean:17`) and lengths `k ≤ 2`
    (`Submission/Primes/SmallProgressions.lean`).

  Ordered removal, relative counting and the linear-forms estimate for the majorant do not depend on
  the set of primes.
- No vendored file needs changing. The dense form needs about 700–900 new lines in about 7 new files
  that import the vendored library. About 350 of those lines are adapted copies with Apache
  modification notices. The rest is new: one elementary analytic lemma (a dyadic "window lemma"
  turning positive relative upper density into frequent mass in a window `(Z/2, Z]`) and glue.

## Answer to question 2

**The relative counting step is general.**
`relativeAPCount_lower_bound_of_linearFormsCondition` (`Submission/Transference/RelativeSzemeredi.lean:114`)
holds for any `f : ZMod N → ℝ` with `0 ≤ f ≤ ν` and `δ + error ≤ mean f`. The comparison hypothesis
`RelativeAPComparisonLe` (`:40`) quantifies over every such `f`, and the parameter package and the
dense count accept any `δ > 0`. The original fixes `δ = densityTarget` at one point
(`Submission/GreenTao/FinalTransferenceAssembly.lean:62`) and uses only `densityTarget_pos` there.

One change of shape is needed. The original gets density at every large modulus, and its transference
predicate exposes only "there exists a large prime modulus". A set of positive upper density is dense
only along a sequence of scales. So the A-version restates the transference for **every** large prime
modulus and every `f ≤ wTrickedPrimeWeight`. The existing proof already shows this; it is a
one-quantifier change. It then picks the modulus with Bertrand's postulate, from a good scale of `A`.
No lower bound for `A` in every residue class is needed: the sieve side is uniform over all reduced
classes, and one pigeonholed class suffices.

## Plan (details in the doc, §§3–7)

1. Window lemma and Chebyshev bounds for `π`, Mathlib-only (the only new mathematics).
2. `wTrickedSetWeight A α W b = 1_A(Wn+b) · wTrickedPrimeWeight α W b`, with its nonnegativity, upper
   bound and positivity lemmas.
3. `HasPrimeModulusSubweightCounts`: the transference for every `δ > 0`, every large prime modulus,
   every sub-weight. Adapted from `ReducedResidueCofinalTransference.lean:55` and
   `FinalTransferenceAssembly.lean:56`.
4. Density selection for `A`: the residue pigeonhole over `A`'s primes in `(X/4, X]`, and the mean bound
   `α c₂/32`. Adapted from `WTrickDensity.lean:145–341, 534`.
5. Extraction for `A` (adapted from `Primes/Extraction.lean`). Lengths `k ≤ 2` by truncating the
   length-3 progression.
6. Assembly, then the bridge `ZInQ.greenTaoDense : ZInQ.GreenTaoDense` in `ZInQKernel/External/`.

First step: the scratch file `scratch/gt-dense-plan/Window.lean` proving `frequently_window`.
Success criterion: it compiles against the repository's Mathlib with no `sorry` and standard axioms.

## Optional Lean check

(Updated at the end of the run; see below.)
