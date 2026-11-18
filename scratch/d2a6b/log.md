# d2a6b results log

Base: fork main d435851d; merged origin/wip/d2a6-reroute (698c8c9e) and origin/wip/y3-route-a (6558e2ff), both clean
(merge commits f72326f9f, 41f61097c).

## Step 1: A6 on Y3FullThreeRepZ30

- Comparison (VERIFIED by reading the Lean files):
  - A6IntModel's `hasGoodReduction_of_intModel` uses ShimuraIntegralModelRep only at p: (i) the universal property at
    the one base `Spec K` (K ⊇ ℚ, a field; locally noetherian) for the object `qml3AsQMAb_of PK`; (ii) properness of
    `𝒴 → Spec ℤ_(p)` (valuative criterion); (iii) the universal family's proper/smooth/geomConn/grp/one_eq;
    (iv) uniqueness of maps to Spec ℤ_(p).
  - Y3FullThreeRepZ30 gives: 𝒴 proper smooth over ℤ[1/30], universal `QMAbSchemeP` (Mumford-form level), universal
    property on locally noetherian ℤ[1/30]-schemes for `QMAbSchemeP` objects.
  - Objects: QMAbScheme (kernel level: injective on field fibres) vs QMAbSchemeP (printed level: bijective onto A_s[3]
    at geometric points). Bridges, both already proved in the tree: `Y3Fix.toKer` (P → kernel, same QMFamily, any base)
    and `Y3Fix.ofKer hT` (kernel → P over ℚ-schemes, from the proved mumfordTorsionAlgClosed). A6 needs the bridge only
    at Spec K, a ℚ-scheme. No new bridge; nothing on the spot.
  - Polarization: both leaves are polarization-free (both carry the same relative-Lemma-P reading point).
  - Primes: ℤ[1/30] model covers every p ∤ 30 ⊇ {p > 324}; `not_dvd_thirty_of_lt`.
- New file ZInQKernel/Contrib/OneProof/A6Z30.lean: spec_to_Z30_ext, z30To, not_dvd_thirty_of_lt, z30ToLocal,
  hasGoodReduction_of_z30, qmModelG3U_of_z30, modelG3G6_of_leavesU_z30.
- D2A6Wrap.lean edited: R6U := RaynaudWildNF ∧ Y3FullThreeRepZ30; modelG3G6_of_leaves3U and good_of_QML3U use the z30
  theorems.
- `lake build ZInQKernel.Contrib.OneProof.A6Z30`: success (14376 jobs, 0 errors; build-a6z30.txt). VERIFIED axioms
  [propext, Classical.choice, Quot.sound] for spec_to_Z30_ext, z30ToLocal, hasGoodReduction_of_z30, qmModelG3U_of_z30,
  modelG3G6_of_leavesU_z30.

## Rebase onto fork main f3402e89 (fold-b112; host's late note)

- `git merge f3402e89` clean (merge commit fdd1502a7). New top: TailZ83 `sixContactMin_of_open76` on
  `OpenResearchLeaves57` (30 fields); `silverbergZarhinThm35` and `y3FullThreeRepZ30` are bundle fields; bost-gr9's
  bypass (TailZ80) copied the research bundles `OpenResearchLeaves53 … 8EB` into `HDec.HSyn.GR9` (same short names).
- Chain top moved to TailZ80's `HDec.HSyn.sixContactMin_of_open73` (bundle `OpenResearchLeaves54`): TailZ81-83 are
  field-by-field conversions (raynaudSemistableSHOr from SZ 3.5, y3FineModuliAbP from Y3Z30, carayolThmAIrr from
  carayolThmAFrob), so the bypass maps `OpenResearchLeaves57`'s successor directly to `OpenResearchLeaves54U`.
- gen_chain.py: TOP = open73, module order from TailZ80, carrier files matched by namespace (GR9 copies).
- gen_bypass.py: CHAIN_R = OpenResearchLeaves54, conversion of `carayolThmAIrr` added; `--mode post` (both
  `silverbergZarhinThm35` and `y3FullThreeRepZ30` mapped).
- build-a6z30.txt trimmed to its A6Z30/axioms/"Build completed" lines.

## Step 2 on f3402e89: taint, chain, bypass (VERIFIED)

- `lake build TailZ83 D2A6Wrap`: success (15395 jobs); `sixContactMin_of_open76` standard axioms.
- TaintD (closure of open76: 274529 constants): IX35 tainted 101, COR33 tainted 96 (taintD-out.txt).
  TaintD2: 31 carriers, now the `HDec.HSyn.GR9.*` copies 8EB…36EBCF plus OpenResearchLeaves54/55/56, 2EB, 5EB, 7EB,
  ResearchLeaves3EB (taintD2-out.txt).
- gen_chain.py → ZInQKernel/Contrib/OneProof/D2A6Chain.lean: 103 declarations (91 from TailZ80's GR9 chain, 25
  EichlerBoundCopy, 9 TailH, 7 HomFree Consumers ... see gen/copied.txt) + 29 structures; edits r14 1, qml3 1.
  `lake build ZInQKernel.Contrib.OneProof.D2A6Chain`: success (15390 jobs), `sixContactMin_of_open73_u`:
  [propext, Classical.choice, Quot.sound] (build-chain.txt).
- gen_bypass.py --mode post → BypassFold.lean: OpenResearchLeaves57 (27) → OpenResearchLeaves58 (27), top
  `sixContactMin_of_open77`; removed sga7_IX_3_5_ForwardGeom_Def34, added elliotWildInertiaTrivial, mapped
  silverbergZarhinThm35 (raynaudSemistableSHOr := raynaudSemistableSHOr_of_sz35) and y3FullThreeRepZ30.
  Count (kinds.tsv of f3402e89): strict 5/24 on 29 → 5/24 on 29; strictest 5/24 → 5/24. Count-neutral.
  `lake env lean scratch/d2a6b/BypassFold.lean`: 0 errors; `sixContactMin_of_open77`: standard axioms (bypass-out.txt).

## Closure check and Step 3 PruneScan (VERIFIED)

- ClosureCheck.lean (bypass module + check), `lake env lean`: closure of open77 274360 constants. Absent:
  SGA7_IX_3_5_ForwardGeom_Def34, SGA7_IX_3_5_ForwardGeom, both RaynaudCriterionNF, GapNeron.RaynaudCriterionNF,
  QML3.goodReduction, raynaudPlace_of_R6, torsFix_of_descent, modelG3G6_of_leaves3, good_of_QML3,
  **SGRSplit.ShimuraIntegralModelRep**, sorryAx. Present: RaynaudWildNF, ElliotWildInertiaTrivial,
  SilverbergZarhinThm35, Y3FullThreeRepZ30, Y3FineModuliAbP (through y3FineModuliAbP_of_z30), RaynaudSemistableSHOr
  (through raynaudSemistableSHOr_of_sz35), SGA7_IX_Cor3_3_Def34. Control open76: old ones present,
  ShimuraIntegralModelRep absent. Residual name: ReductSplit.SemistableUnipotent._proof_2 (auxiliary proof term).
- PruneScan (PruneScanBypass.lean, 9m21s): top-level fields unused: base open76 0 of 27+0+2; bypass open77 0 of
  27+0+2. Prune set empty in both. Live chain bundles (the U copies) have exactly the unused fields of their
  originals in base (prunescan-summary.txt): no field lost its last reader. `mulEtaleAbelianScheme` is a field only
  of the old textbook generations OpenTextbookLeaves7-10, unused in base and bypass alike (on this base the live
  textbook bundle OpenTextbookLeaves18 has 0 fields); nothing to prune.

## Step 4 and #discharges on f3402e89 (VERIFIED)

- `lake build Main Discharges D2A6Chain`: success (15992 jobs). Discharges.lean (`lake env lean`): 34 `#print axioms`,
  all [propext, Classical.choice, Quot.sound] (D2WildNF 12, A6IntModel 10, wrappers 5, A6Z30 6, chain top 1).
- `#discharges`: 150 lines; 135 are projections of the copied `…U` structures (noise); the other 15 are pre-existing
  conditional discharges of base fields (carayolThmAFrob, dsThm965Printed, deRhamVpAbVarDirect, pazukiCor13Upper, …),
  none about this task's fields. The IX 3.5 bypass is not a discharge.
- Strict dry run: no field is discharged outright on f3402e89 (raynaudSemistableSHOr and y3FineModuliAbP were the two
  outright discharges on TailZ79; both are folded on this base, TailZ81/82). `autofold.py tailz79/autofold.json
  --dry-run` now refuses: "not a field of the current bundles" (strict-dryrun-f3402e89.txt). The bypass count uses
  autofold.py's own `counts` and `render_open.must_be_glue` (gen_bypass imports autofold.py): 5/24 on 29 → 5/24 on 29.
- TailZ79-era dry runs and bypass variants archived in scratch/d2a6b/tailz79/.
