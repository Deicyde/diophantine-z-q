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

## R5Count.lean (04:00-04:20)
- `scratch/height-split/R5Count.lean` imports `ZInQKernel.HDecomp.QM.Leaves`; `lake env lean`: exit 0,
  no errors (VERIFIED, ~6 s). `#print axioms r5fpCount_of`: `[propext, Classical.choice, Quot.sound]`.
- New definitions: `OptEmb` (optimal embeddings `k → B`, `φ⁻¹(O) = R`), `embSetoid` (conjugacy by
  `Oˣ`; equivalence proved), `eichlerFactor` (2 inert / 1 ramified / 0 otherwise), `QMClasses`.
- Leaf `EichlerOptimalEmbeddingCount` (Eichler 1955 / Vignéras III 5.11-5.12 / Voight ch. 30, numbers
  UNVERIFIED; caveat: some sources count mod O¹ with factor 2). Glue `QMPairEmbeddingCorrespondence`
  (Shimura uniformization; an Equiv). Proved `r5fpCount_of : Eichler → Correspondence → R5fpCount`.

## MetrizedDimUnique proved (04:40-05:00)
- `scratch/height-split/DimUnique.lean` (dev file, imports `ZInQKernel.HDecomp.Faltings.Height`):
  `card_sq_eq_one_of_uniformization` (`#{p : p² = 1} = 2^{2g}` for a surjective hom `ℂ^g → P` with
  kernel a full lattice; via `Setoid.quotientKerEquivOfSurjective`, `AddSubgroup.index_range_nsmul`,
  `ZLattice.rank`) and `metrizedDimUnique_aux`. Compiles, axioms standard (VERIFIED).
- Merged into `HeightSplit.lean` as `metrizedDimUnique : MetrizedDimUnique`; corollaries
  `stableHeightFinite_of'` (H-19 from N1, SS1, SS2, NeronMetrizable, AN3U) and `r21_of_leaves'`
  (H-17 from Bost, N1, SS1, SS2, AN3U). Full file recompiled: no errors, all axioms standard (VERIFIED).
- 05:10 R22: added leaf `PazukiCor13Upper` (upper half of the same display), `pazukiCor13Upper_of`, `r22_of_upper`; `r22_of_leaves` now via the upper half. Recompiled clean, axioms standard (VERIFIED).
