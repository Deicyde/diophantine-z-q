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
- 11:33 Reduction.lean §7: leaf `SerreTateThm2` (Serre–Tate 1968 Thm 2, finite image of inertia on T_ℓ), glue
  `TorsionFieldOfDefinition`; proved `finite_image_of_open` (⇐ direction of the finite-image/open-subgroup equivalence,
  no glue) and `open_of_finite_image` (⇒, from the glue + divisibility); `serreTatePotentialGood_of_leaves : SerreTateThm2 →
  TorsionStructure → TorsionFieldOfDefinition → PkgI2.SerreTatePotentialGood.{0}`. OK 10 s. Axioms of the three row
  theorems: [propext, Classical.choice, Quot.sound]. VERIFIED.
- 11:38 §8: `GroupModelO.transport`, `semistableNeronModels_transport`, `bcbcIso` (`(A_{K'})_L ≅ A_L` via Mathlib's
  `mapGrpCompIso`, `mapGrpNatIso (Over.pullbackComp ..)`), `bcbcIso_isMonHom`: OK. VERIFIED.
- 11:40 `SemistableReductionDVR` restated at every place of `K'` over `O` (the printed scope; r8 uses the place `w ∩ K'`).
  §9: leaf `SemistablePersistsDVR` (SGA 7 IX 3.3, finite extensions), glue `DVRComapFinite`, `SemistableLocalGlobal`,
  `SemistableAlmostAll`; `semistablePersists_of_leaves : ... → ZInQ.HeightSplit.SemistablePersists`,
  `semistableReductionThm_of_leaves : ... → ZInQ.HeightSplit.SemistableReductionThm`: OK 11.5 s; all five row theorems
  depend on [propext, Classical.choice, Quot.sound]. VERIFIED.
