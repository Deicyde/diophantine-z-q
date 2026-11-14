# reduct-split results log

Setup: compile checks with `scratch/reduct-split/chk.sh FILE` = `lean` with LEAN_PATH on a symlink tree
`~/rs-lib` of ~/dzq-check2's build (same commit 5da857b0, `git diff 5da857b0 HEAD -- ZInQKernel` empty) plus
`ZInQKernel/OneProof/H/TailY.olean` compiled out of tree (17 s, unchanged source). One Lean process at a time.

## Compile outcomes
- 11:25 Reduction.lean §1 (divisibility: `exists_pow_eq`, `exists_tate_lift` from `PkgI2.TorsionStructure.{0}`): OK, 4 s. VERIFIED.
- 11:30 Reduction.lean §2-§6: definitions `GroupModelO`, `IsNeronModel`, `geomSpecialFibre`, `IsSemistable`,
  `SemistableNeronModels`, `HasSemistableReduction`, `TΩ`, `galTΩ`; leaves `NeronSchemeModelExistsDVR` (BLR 1.4/3),
  `SemistableUnipotent` (SGA 7 IX 3.5 ⇒), `RaynaudSemistable` (SGA 7 IX 4.7), `SemistableReductionDVR` (SGA 7 IX 3.6);
  glue `DVRFiniteExtension`, `FixedTorsionRational`; theorems `raynaudCriterion_of_leaves : ... → PkgI2.RaynaudCriterion.{0}`,
  `grothendieckMonodromy_of_leaves : ... → PkgI2.GrothendieckMonodromy.{0}`: OK, 8 s. VERIFIED (axioms not yet printed).
