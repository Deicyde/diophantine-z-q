# height-split results log

Task height-split (2026-11-14). Base cba8157f. Lean files: scratch/height-split/*.lean, each checked
with `lake env lean` (one process at a time). Marks: VERIFIED / STANDARD / SPECULATIVE / UNVERIFIED.

## Setup
- 03:15 `lake build ZInQKernel.HDecomp.Faltings.Leaves ZInQKernel.HDecomp.LeafPush2.Bridge
  ZInQKernel.Contrib.HeightBC.Main ZInQKernel.HDecomp.QM.Leaves`: success (VERIFIED).
- Rows located (VERIFIED, read): R18 `ZInQKernel/HDecomp/LeafPush2/R18.lean`, R22 `.../R22.lean`,
  R20/R21 `ZInQKernel/HDecomp/Faltings/Leaves.lean`, StableHeightFinite `.../Faltings/Height.lean`,
  R5fpCount `ZInQKernel/HDecomp/QM/Leaves.lean`. All rows live under ZInQKernel/, so they are imported.
- Existing H5 infrastructure (VERIFIED, read): kernel leaves N1 `H5Neron.NeronModelExists`,
  N2 `H5Neron.SemistableNeronIdentityComponent`; theorems `Contrib.HeightBC.modelHeightBaseChange`,
  `openSubgroupHeight`, `neronModelMinimal`, `H5Neron.groupModelBaseChangeExists`,
  `stableFaltingsHeight_eq_neron_of_N1N2`.

## HeightSplit.lean (03:20-04:00)
- `scratch/height-split/HeightSplit.lean` imports `ZInQKernel.HDecomp.LeafPush2.R22` and
  `ZInQKernel.Contrib.HeightBC.Main`. `lake env lean`: exit 0, no errors, no warnings (VERIFIED, ~10 s).
- 10 `#print axioms`: all `[propext, Classical.choice, Quot.sound]` (VERIFIED).
- New definitions: `algPt`, `algPtMap`, `HasSemiAbelianIdentityComponent`, `ResBar`, `geomFibre`,
  `IsSemistable`, `IsStableFaltingsHeight`, `mulHeightL2`, `absLogHeightL2`.
- Leaves (published form; locators UNVERIFIED unless read by locators.md): `SemistableReductionThm`
  (SGA 7 IX 3.6, global form), `SemistableNeronBaseChange` (SGA 7 IX 3.3), `BostLowerBound`
  (Deligne normalization, display UNVERIFIED), `JavanpeykarBound`, `FaltingsLemma5` (semistable
  form), `PazukiCor13` (two-sided, l2 theta height). Kernel leaf reused: N1 `NeronModelExists`.
- Glue (named, unproved): `NeronMetrizable`, `MetrizedDimUnique`, `IsogenySemistableBaseChange`;
  kernel Prop reused: `AnalyticUniformizationUnique`.
- Proved: `stableFaltingsHeight_eq_of_semistable`, `isStableFaltingsHeight_iff` (H5 identification),
  `isStableFaltingsHeight_unique`, `semistableNeronIdentityComponent_of` (kernel N2 from N1+SS1+SS2),
  `stableHeightFinite_of` (H-19), `r21_of_leaves` (H-17), `grBostBound_of_bost`
  (`log(2π)+log π < 3`), `r18_of_leaves` (H-14), `r20_of_leaves` (H-16), `r22_of_leaves` (H-18),
  `absLogHeight_le_absLogHeightL2`, `pazuki_upper_of_two_sided`.
