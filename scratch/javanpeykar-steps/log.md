# javanpeykar-steps results log

Base: main e1b31749 + merge of origin/wip/leaf-fold33b (c66e1c024; was not on main). Build tree copied from
~/dzq-wt/sga33-steps (.lake/build and lean/.lake), lake rebuilds only changed sources.

Target: `HDec.HSyn.OpenResearchLeaves39.javanpeykarPrintedMapHF : JavanpeykarRebase.JavanpeykarPrintedMap`
(ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean:200; kind consequence, GLUE).

## Step A: the restated leaf and the instance (VERIFIED, compiled)

scratch/javanpeykar-steps/JavanpeykarThm111.lean (`lake env lean`, 7 s, no errors):
* defs `IsBelyiMorphism` (finite; restriction over P1 minus {0,1,inf} LocallyOfFiniteType and Mathlib
  FormallyUnramified; degree finrank of k(C) over the stalk at beta(eta)), `IsBelyiDegree` (IsLeast of
  positive Belyi degrees), `genus` (arithmeticGenus over the base), `IsStableHeightBar` (printed stable
  height of a model over a number field L with Algebra L Qbar), leaf `JavanpeykarThm111`.
* `isBelyiMorphism_of_isBelyiMap` (step 3): stalkwise via `HasRingHomProperty.of_stalkMap` +
  `RingHom.FormallyUnramified.ofLocalizationPrime`; residue extension finite from quasi-finiteness
  (`Scheme.Hom.quasiFiniteAt`, `Module.Finite.of_quasiFinite`), separable by char 0; max ideal from the
  IsBelyiMap clause at closed points, automatic at the generic point (field).
* `exists_isBelyiDegree_le`, `javanpeykarBound_mono` (step 2).
* `javanpeykarPrintedMap_of_thm111 : JavanpeykarThm111 → JavanpeykarRebase.JavanpeykarPrintedMap`
  (no other hypothesis). Axioms: [propext, Classical.choice, Quot.sound].
## Step B: (H2), (H3) (VERIFIED, compiled)

* `dim_eq_of_iso`, `isPrintedStableHeight_of_iso` (javanpeykar-dict `transport`; defeq of the printed
  metric data accepted by `exact`), `isStableHeightBar_of_iso`.
* `isPrintedStableHeight_unique (hT35 hGC hN1 hSS2)`: from `ZInQ.HeightFix.isStableFaltingsHeight_of_printed`
  (checked: hypotheses T35 = ZInQ.LeafPush2.UniformizationExists and AVGlue.GeomConnOfRationalPoint) and
  `ZInQ.HeightSplit.isStableFaltingsHeight_unique` (ZInQ.H5Neron.NeronModelExists, SemistableNeronBaseChange).
  GeomConnOfRationalPoint is proved (`geomConnOfRationalPoint_proof`).
* Copied verbatim to ZInQKernel/Contrib/OneProof/JavanpeykarThm111.lean.
## Step C: #discharges and fold dry run (VERIFIED)

* lake build +Main +Discharges +Contrib.OneProof.JavanpeykarThm111: success, 14289 jobs (build_out.txt).
* #discharges (discharges_out.txt): DISCHARGES [OpenResearchLeaves39.javanpeykarPrintedMapHF] by
  JavanpeykarSteps.javanpeykarPrintedMap_of_thm111; still assumes [JavanpeykarSteps.JavanpeykarThm111];
  standard axioms.
* autofold --dry-run: strict 17/16 -> 18/15 on 33, strictest 17/16 -> 18/15. Generated module compiles,
  sixContactMin_of_open57 standard axioms (FoldDryRun.lean.txt).
