# g10-odd results log

## Statements
- `G10Glue` copied verbatim (scratch/g0-mod-galois/part_galois.lean L223-242) into
  scratch/g10-odd/G10Odd.lean §1, with `HSyn.T11_RiemannGAGA`, `HSyn.T12_ArtinComparison`
  (opaque, verbatim from scratch/g0-split/Split.lean L19261-19268), `resQ`, `Vb`, `tate`,
  `Intertwines`, `G10Out` (verbatim). `PkgI3.*`, `PkgI4.*`, `GlueI3.repBaseChange` imported from
  ZInQKernel/HDecomp (bodies identical to Split.lean's copies; diffed: only docstring line breaks
  and extra defs differ). VERIFIED (diff).

## Findings
- F1 (VERIFIED, by reading): `HSyn.T11_RiemannGAGA`, `HSyn.T12_ArtinComparison` are `opaque … : Prop`:
  no content can be extracted from them; any proof of `G10Glue` must not use them.
- F2 (VERIFIED, compiled): `G10Glue` follows from `ConjTwistNontrivial` (new named glue, stated over
  `PkgI3.AbVar.galRep`, `resQ`, `PkgI4.IsComplexConj`), with `PkgI3.FaltingsTate` as its only
  hypothesis. Theorem `G0Galois.g10Glue_of_conjTwist`.
- F3 (VERIFIED, compiled): algebra: `det_eq_neg_one_of_sq_eq_one`, `isComplexConj_mul_self`,
  `isOdd_of_not_pm_one`, `baseChange_injective'`, `galRep_eq_of_central`.

## Compile outcomes
- 2026-11-13 04:18 `lake env lean scratch/g10-odd/G10Odd.lean`: no errors, no warnings (after
  `lake build ZInQKernel.HDecomp.LeafPush2.T ZInQKernel.HDecomp.I3Linalg.C2`).
- 2026-11-13 04:24 §4-§5 added (T12K split, totally real case, corrected statement): compiles,
  no errors. New: `T12K_ComplexConjEigen` (glue target), `ConjTwistOutside` (glue),
  `not_pm_one_of_mem_range`, `g10Glue_of_T12K_conjTwistOutside`, `isOdd_of_T12K_of_forall_mem`,
  `G10GlueConcrete`, `ConjTwistFromLeaves`, `g10GlueConcrete_of_conjTwistFromLeaves`,
  `g10Out_of_conjTwist` (the conclusion without the opaque hypotheses). VERIFIED (compiled).
