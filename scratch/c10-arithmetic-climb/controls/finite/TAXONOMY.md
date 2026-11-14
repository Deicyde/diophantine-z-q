# Finite-coefficient-field validation taxonomy, v1

Status when authored: primary six-body proof compiled by ParentA; checks/controls not run yet. The source author runs no Lean on OD and does not attach to ParentA. Execution and raw diagnostics belong to the sole-parent fresh-worker task.

## Positive/conformance source: FCF_Checks.lean

- Six bare theorem assignments to the **verbatim frozen F1–F6 expressions**, mechanically extracted from target SHA256 `66c85645fd3a4b4036208be83910661b45a903e6f443d87e31100fc923d405f0`. No new expected-field predicate or FD assumption is introduced.
- Six explicit `#check @` commands expose full theorem binders, and six `#print axioms` commands inspect the selected exports. The allowed standard set is `{propext, Classical.choice, Quot.sound}`; a subset is fine. This is not a fresh proof replay of all imported Mathlib.
- `PEmptySet`: the actual adjoin of an empty generating set, including its least-field and fixed-place clauses.
- `PRepeated`: a GIVEN `a : Qbar` repeated over `Fin 3`; every index and its fixed-place image are recovered. No three-distinct-values/count claim.
- `PVaryingMatrices`: GIVEN matrices over `Fin 2` with row size k+1 and column size k+2; the full scalar + all-k/i/j matrix result, not one coordinate.
- `PEmptyMatrixFamily`, `PZeroRows`, `PZeroColumns`: GIVEN empty-domain matrix data, the same single E, and the full result; no hidden Nonempty premise.
- The variable `a` is not labeled a constructed quadratic/nonrational witness. No new coefficient preimage, normalization, original C10 matrix, basis, or actual coefficient-field identification is manufactured.

## Structural negative files

Run only **after** FCF_Proof and FCF_Checks import/compile successfully. Every negative is expected to exit nonzero for the listed source-level cause; an import/cache/bootstrap failure is not an accepted control result. Retain each exact input and its first raw diagnostic before any edit.

- `neg/BadNoFiniteSet.lean`: missing `s.Finite`; the producer is still a function awaiting that certificate. Expected type mismatch.
- `neg/BadNoFiniteFamily.lean`: missing `[Finite ι]` for F4. Expected instance-synthesis rejection.
- `neg/BadNoFiniteMatrixFamily.lean`: missing `[Finite κ]` for F5 while both coordinate types are `Fin 1`. Expected instance-synthesis rejection.
- `neg/BadNoFiniteRows.lean`: κ and columns are finite, but row type R has no Finite certificate. Expected row-instance rejection.
- `neg/BadNoFiniteColumns.lean`: κ and rows are finite, but column type C has no Finite certificate. Expected column-instance rejection.
- `neg/BadReplacementValue.lean`: the producer recovers the original GIVEN a, while the consumer demands unrelated b. Expected equality-type mismatch.
- `neg/BadSecondPlace.lean`: restriction uses ρ′ but the consumer demands ρ a without any relation between the two places. Expected equality-type mismatch.
- `neg/BadComplexInput.lean`: attempts to feed a finite `Set ℂ` to the literal-Qbar producer. Expected `Set ℂ` / `Set Qbar` mismatch; finite complex data do not silently supply algebraicity/preimages.

These are **typed contract-rejection fixtures, not mathematical counterexamples**. In particular, an infinite index or coordinate type can have a finite value range if that is separately supplied; this frozen producer asks for finite indices. No necessity, transcendental, unequal-value, or inequivalent-place witness is claimed.

## Evidence requirements

Bind each source SHA256/byte count, frozen target hash, exact input/output paths, imported compiled module names, argv, exit status, stdout/stderr/time, and selected axiom output. Retain FAAS_CONTAINER_MEM_SOFT_LIMIT and memory evidence from ParentA, preferably per-run RSS samples plus peak RSS. At most one serial `-j1` per author lane and at most two high-RSS jobs per 32-GiB node. Cache/transport or type-ascription acceptance alone is not the complete primitive verification.

All frozen target bytes remain unchanged. New proof/test source is versioned and immutable before execution; a failed input/log remains retained when a later source version is written. No PR/main/pin/workflow/manuscript or global C10/Tate/LC claim follows.
