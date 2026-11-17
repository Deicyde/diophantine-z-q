# height-fix log

Base: wip/height-dict 15cc5a60, merged origin/main (0caafe66, STATUS.md only) -> 4d9056fc.

## 2026-11-16
- 13:20 `lake build ZInQKernel.Contrib.OneProof.HeightDictionary`: OK (12753 jobs). VERIFIED.
- Plan: new file ZInQKernel/Contrib/OneProof/PrintedFaltingsHeight.lean (namespace ZInQ.HeightFix), importing
  HeightDictionary. HeightDictionary.lean itself is not edited (javanpeykar-fix merged it).
- Fix1.lean compiles (VERIFIED): `eq_of_density` (two finite measures on a compact space with the same local
  densities in charts are equal), `DensAt`, `densAt_map`, `densAt_of_invariant`, `eq_of_densAt`,
  `isMulLeftInvariant_of_densAt`; defs `chartAt`, `HasFormDensityAt`, `IsFormMeasure`, `IsPrintedMetricSq`
  (existence AND uniqueness of the mass); `metrized_setup`, `isFormMeasure_iff` (invariance proved),
  `isPrintedMetricSq_iff` (printed metric = torusMetricSq for eta != 0).
- Merged origin/wip/dict-models (ca225d00) for `DictModels.RaynaudOr.HasSemiAbelianIdCompTorus` and
  `hasSemiAbelian_pullback_bar`; `lake build ZInQKernel.Contrib.OneProof.RaynaudSemistableOr` OK.
- Fix1.lean compiles (VERIFIED) with: `existsUnique_isPrintedMetricSq` (T35; every group model, eta != 0),
  `exists_chart` (translated algebraic coordinates are charts: IFT + Phi injective/open on a ball),
  `IsSemistableRes` (k(p) form), `isSemistable_of_res` (ascent, 04KV), glue `SemiAbelianDescendsPerfect`,
  `perfectField_residueField`, `isSemistableRes_of_geom`, `IsPrintedStableHeight`, `BostLowerBoundPrinted`,
  `GaudronRemondThm14Printed`, `isPrintedStableHeight_of` (needs hT35, hD), `isStableFaltingsHeight_of_printed`
  (hT35, hGC; no NeronMetrizable hypothesis), `isPrintedStableHeight_iff`, `bostLowerBound_of_printed`,
  `gaudronRemondThm14_of_printed`, `*_of_kernel` (new leaves follow from old rows).
- FINDING: the consumer direction (kernel height => printed height) needs geometric => k(p) semistability
  (descent from kbar to the finite residue field: Chevalley over perfect fields). Not provable here; stated as
  glue `SemiAbelianDescendsPerfect`. dict-models' step is the ascent k(p) => kbar, used for printed => kernel.
- ZInQKernel/Contrib/OneProof/PrintedStableHeight.lean (42 KB): `lake build` OK (12770 jobs). VERIFIED.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: OK (13698 jobs; frozenTarget standard axioms).
- PrintedStableHeight.lean with `chartAt_comp`, `chartAt_comp_hasStrictFDerivAt`, optional Javanpeykar/Pazuki rows:
  build OK. VERIFIED.
- `#discharges` (scratch/height-fix/discharges.txt): bostLowerBound, gaudronRemondThm14 (and optional
  javanpeykarBound, pazukiCor13Upper) discharged by ZInQ.HeightFix.*_of_printed, still assuming the printed leaf,
  UniformizationLeafAll, MumfordTorsionAlgClosed, SemiAbelianDescendsPerfect; standard axioms; no sorry. VERIFIED.
- autofold dry run: without --allow-rise refuses (34/11 -> 34/12 on this base, where both rows are still LEAF);
  with --allow-rise exit 0. FoldDryRun.lean (output minus line 1) compiles, sixContactMin_of_open36 standard
  axioms. VERIFIED. Against the re-rated base (rows GLUE): 32/13 -> 34/12, i.e. -1 GLUE.
