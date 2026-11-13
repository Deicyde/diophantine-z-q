# g0-heightadd (fleet note)

**Verdict.** `HSyn.G0Split.HeightAdditivity` (glue E4, `h(A) + h(Z) ≤ h(A × Z)`) is neither false
nor vacuous. It is proved in Lean, with g0-split's exact statement, from:
- leaf N1 `NeronModelExists` (BLR §1.4 Thm 3, UNVERIFIED locator; new, not in the bundles);
- the bundle field `ResearchLeaves.h5` (only `NeronModelMinimal` is used);
- def-faltings' stated `AnalyticUniformizationUnique`;
- three new glue Props: `MetrizationDimUnique`, `MetrizationExists`, `ProductMetrizationGeo`.

The theorem is `heightAdditivity_of_geo`. The coarser forms `heightAdditivity_of` (from h5-neron's
`ProductModelHeight`) and `heightAdditivity_of_split` (from `ProductMetrization`) are also proved.

**Gap check.** h5-neron's `stableFaltingsHeight_add_le'` was not literally the piece, in three
ways, all now closed in Lean:
- it is over `PkgI3.AbVar`, not def-faltings' `AbVar`; its proofs recompile unchanged over the latter;
- it uses `IsProductAbVar` where the piece has `IsProductOf` (bridge proved);
- it is stated in `EReal`, the piece over `ℝ`.

Its remaining glue `ProductModelHeight` is reduced in Lean to the four Props above. The
Arakelov-degree half is proved: `modelHeight_add_of`, model heights add when index, coefficients
and covolumes multiply.

**What compiles** (all axioms `propext`, `Classical.choice`, `Quot.sound`):
- `scratch/g0-heightadd/HeightAdd.lean`. It contains the verbatim def-faltings section of
  `Split.lean` plus `part_heightadd`, `part_zero` and `part_prod`.
- The dimension-0 consistency check of the new glue.
- The integration check `SplitIntegrated.lean`: g0-split's `Split.lean` with the proofs pasted in.
  The piece is closed there from `r.h5`, and `glueOutputs_of_leaves` and `sixContactMin_of_leaves`
  still compile.

**What remains.** Proofs of U, `MetrizationDimUnique`, `MetrizationExists` and
`ProductMetrizationGeo`. They need stalks of fibre products of schemes, the rank of `ω` for smooth
group schemes, and the uniformization `A(ℂ) ≅ ℂ^g/Λ`, none of which are in Mathlib. N1 is a leaf.

Report: `docs/research/g0-heightadd.md`; log: `scratch/g0-heightadd/log.md`.
