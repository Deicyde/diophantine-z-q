# op-dedupe: the H chain on the kernel's declarations

**After this task `scripts/one_proof/gen.sh` no longer reproduces `ZInQKernel/OneProof/H/*.lean`; the library
modules are the source.** They are regenerated from the leaf-fold4 copies (commit a2de2112) by
`scratch/one-proof/redo.sh MODULE a2de2112 DELETED_MODULES...` (deletion, alias opens, the per-module fixes in
`scratch/one-proof/fixes/`).

## Result

* `lake build +ZInQKernel.OneProof.Main` succeeds; `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
* **2951 of the H chain's 7306 declarations removed** (4355 remain); the H chain now uses the kernel's constants for
  every removed copy. Of the 3311 rows of `dedupe_map.tsv`: 2941 removed, 5 are not declarations (the map's
  regex matched text inside comments, e.g. `class field theory;`), **365 KEPT** (below). In addition 6 copies not in
  the map were replaced by hand (def-faltings' `ZInQ.DefFaltings.AbVar` structure with its `baseChange`, `dim`,
  `ZInQ.H5Neron.AbVar.zero`, by the kernel's alias `ZInQ.DefFaltings.AbVar := PkgI3.AbVar`; and LF2UnramConj's
  root `G0ModField.numberField_of_fd`, by the kernel's in `Contrib/FrobChain/TateBridge.lean`).
* LF2Stalks and LF3Cot (49 root-namespace duplicates of `Contrib/HeightBC/{StalkPullback, LocalStructure,
  StalkTensor, CotangentBC}`) are now just imports of those modules, so the chain sits next to HeightBC; the chain
  also imports `Contrib/FrobChain/TateBridge` (it clashed with LF2UnramConj before).
* frozenTarget's hypotheses are the same 66 bundle fields and 9 TYZ/GZ statements. **29 fields are now stated with
  the kernel's Prop** (r1rec, r5, r5count, r6, r7a, r7b, r8, r9a, r9b, r16, r17, r19, r20, r21, h5fin, t3, t4, t5,
  t6, t7, t8, t10, t11b, t27, t33, t34, t35, t38, t41: e.g. `HDec.PkgI2.RaynaudCriterion` became
  `PkgI2.RaynaudCriterion`); the other 37 are H-only definitions or KEPT copies (`fields_before.tsv`,
  `fields_after.tsv` in scratch/one-proof).
* **Discharge: no field and no TYZ/GZ hypothesis is proved in ZInQKernel/** (search below), so there is no
  `frozenTarget_v2`; every field is OPEN.

| module | decls before | after | removed | map rows | KEPT |
|---|---|---|---|---|---|
| LPrefix | 2524 | 802 | 1722 | 1746 | 28 |
| TailA | 573 | 282 | 291 | 297 | 6 |
| TailB | 656 | 527 | 129 | 129 | 0 |
| TailC | 1212 | 896 | 316 | 617 | 301 |
| TailD | 25 | 25 | 0 | 0 | 0 |
| LF2Stalks | 43 | 0 | 43 | 43 | 0 |
| LF2UnifRoot | 7 | 7 | 0 | 0 | 0 |
| LF2SmoothDim | 34 | 34 | 0 | 0 | 0 |
| LF2UnramConj | 6 | 5 | 1 | 0 | 0 |
| TailE | 531 | 362 | 169 | 176 | 7 |
| LF3Cot | 6 | 0 | 6 | 6 | 0 |
| TailF | 244 | 199 | 45 | 46 | 1 |
| TailG | 496 | 464 | 32 | 32 | 0 |
| TailH | 477 | 280 | 197 | 219 | 22 |
| TailI | 17 | 17 | 0 | 0 | 0 |
| LF4T5 | 96 | 96 | 0 | 0 | 0 |
| TailJ | 336 | 336 | 0 | 0 | 0 |
| TailK | 23 | 23 | 0 | 0 | 0 |
| total | 7306 | 4355 | 2951 | 3311 | 365 |

(Declarations counted by `dedupe_map.py`'s scanner; "removed" includes the 6 hand replacements and the map rows in
comments are not declarations.)

## Why a text map is not enough, and the check used

Same name and same text can denote different constants: `HDec.GlueAssembly.PazukiOutput` is the hardened `+ 3`
version while the kernel's has `log π`, so every copy whose text mentions `PazukiOutput` means something else in
the kernel; leaf-push2's copies (`HDec.ZInQ.LeafPush2.stableFaltingsHeight`, `IsCurve`, ...) resolve in the kernel
to `ZInQ.DefFaltings` / `LeafModCurves`. So each mapped copy was checked at the level of constants
(`scratch/one-proof/FaithCheck.body.lean`): with the original chain compiled to a separate olean tree, a copy
`HDec.n` is FAITHFUL when its type (its value, for definitions; its constructor types, for inductives) equals the
kernel's `n` after renaming every faithful `HDec.m` to `m` (also inside `Expr.proj`), syntactically or by
`isDefEq`; greatest fixpoint (5 rounds). 3164 of the 3262 HDec-namespace rows are faithful, 93 differ, 5 are
not declarations (inputs: `faith_mapped.txt`, `faith_hnames.txt`; result `faith.tsv`). Only faithful copies were
removed, so every hypothesis Prop that changed name is definitionally the H chain's earlier one.

## KEPT copies (365; `scratch/one-proof/kept.txt`, with the reason for each)

* **G9 layer, 294** (TailC, all `ZInQ.Contrib.G9.*`): the kernel's `ZInQ.Contrib.G9` is stated over its own copy
  `ZInQ.Contrib.G9.PkgI4`/`PkgI3`, the H copy over `PkgI4`/`PkgI3`. 22 differ outright; the other 272 agree only up
  to `isDefEq`, and the kept proofs `rw` with them syntactically, so the whole layer is kept.
* **TateBridge35 family, 22** (TailH: `G14Bridge.TateBridge35`, `AlgFrobRedRed.tateBridge35_of_*`,
  `FrobPiecesGood.tateBridge35_of_*`, `FrobTrace.tateBridge35_of_*`): H's `G0ModField.G7Data` (with the
  `[L:ℚ] ≤ D` bound) differs from the kernel's.
* **G7 / TateBridge, 13** (TailA 6: `G0ModField.AfterG7`, `G7OutUnr`, `TateBridge`, `fieldDescentUnr`,
  `galoisG2Out_of_g7Data`, `modularConstituent_of_ranges_T14`; TailC 6 `UnramTate.*` + `G14Trace.FrobTraceLink`;
  TailF `UnramTate.LinkedFrob`), same cause.
* **E1Sub base change, 14** (LPrefix `E1Sub.bcPt*`, `bcPhi*`, `bcT*`, `bcV*`): H's `E1Sub.bcPt` differs.
* **Pazuki / GlueOutputs, 3** (LPrefix `GlueAssembly.GlueOutputs`, `jHeightBound_of_glueOutputs`,
  `sixContactMinAt_of_glueOutputs`): hardened `PazukiOutput`.
* **leaf-push2 copies, 7** (LPrefix `ZInQ.LeafPush2.R03_LinYang`, `R03_LinYang_algClosed`, `R03_of_algClosed`,
  `R18_Javanpeykar`, `R18_real`, `R22_Pazuki`, `R22_plus3`): stated over H's leaf-push2 copies of the curve/height
  objects (the kernel's are over `LeafModCurves` / `ZInQ.DefFaltings`). So fields r3, r18, r22 stay HDec.
* **AbVarBC, 7** (TailE `ZInQ.Contrib.AbVarBC.abVarBaseChange*`): H's `AbVarBaseChangeK` differs.
* **def-faltings, 4** (LPrefix `ZInQ.DefFaltings.IsEllipticCurveOf`, `AcceptanceEC`, `exampleHodge_modelHeight`,
  `exampleHodge_modelHeight_eq_zero`): use H-only `AbVar.origin`/`structMapOn` on the old copy and H's
  `exampleHodge`.

## Discharge (step 4)

`scratch/one-proof/SearchProofs.lean` imports Main and the 78 kernel modules that mention any field or hypothesis
Prop name, and lists every non-HDec theorem whose type is the field's Prop (syntactically or by `isDefEq`, same head
constant): `search_proofs.tsv`. Nothing was found. Status of every field: **OPEN**.

* OpenResearchLeaves2 (26): r1r2 (`HDec.LeafAdopt.R1R2fpRep`), r1b, r1rec (`LeafQM.AV.R1rec`), r3, r4, r5
  (`LeafQM.AV.R5fp`), r5count, r6 (`PkgI2.RaynaudCriterion`), r7a, r7b, r8, r9a (`PkgI3.FaltingsSemisimple`), r9b
  (`PkgI3.FaltingsTate`), r10, r11r12, r13, r14, r15, r16 (`LeafModCurves.R16_EichlerShimuraJ1'`), r17
  (`LadicCond.CarayolR17'`), r18, r19, r20, r21 (`ZInQ.DefFaltings.R19_GaudronRemond`, `R20_FaltingsLemma5`,
  `R21_Bost`), r22, h5fin (`ZInQ.DefFaltings.StableHeightFinite`): all OPEN.
* OpenTextbookLeaves4 (19): t3, t4, t5 (`PkgI2.NeronMappingAbelianScheme`, `ReductionTorsionBijective`,
  `TorsionStructure`; the kernel's `t36_torsionStructure` proves `X1Belyi.TorsionStructure`, a different Prop), t6,
  t7, t8, t9, t10, homLatticeCorr, t11b, t23, t24, t27, t33, t34, t35, t38, x0Transitive, t41: all OPEN.
* OpenAddedLeaves4 (20): cmOptimalEmbedding, thetaRatiosAlgebraic, qmHauptmodul, qmClassNumberOne, senTwist,
  finiteImageHT, t09SymmIsogenyExists, isogenyQuasiInverse, x6ConicModel, y3Connected, qmAutCard, serreRigidity3,
  alFixedPoints, zariskiConnectedness, cmDescends, gammaStarGen, valenceBoundGammaStar, egaIV_8_8_2_ii,
  egaIV_8_10_5_xii, egaIV_17_7_8_ii: all OPEN.
* OpenGlue4 (1): heckeVertWitness: OPEN.
* frozenTarget's TYZ/GZ hypotheses: h11 `TYZThm11Integral`, h1 `TYZLcalOne`, h29 `TYZLemma29Mod2`, hcm
  `CMFieldOfDefinition ringClassFieldD`, hs `TYZSigmaFixesZn`, h318 `Lemma318Literal HHprime`, hG
  `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` (no theorem statement mentions `GenusPointLeafCM`), hL2
  `FHNonvanishing`, hL3 `GrossZagierHeegner`: all OPEN.

## How the edits were made

* `del_decls.py`: deletes one module's map rows (same extents as `dedupe_map.py`, plus attached docstrings and
  `@[..]` / `open .. in` / `include .. in` / `omit .. in` lines; truncated before column-0 non-declaration commands;
  rows inside comments and KEPT names skipped) and imports the supplying kernel modules.
* `add_opens.py`: inside `namespace HDec.A`, `x` never resolves to the kernel's `A.x`, and `open N` opens `HDec.N`.
  After every `namespace` and `open` line inside HDec it adds `open _root_.M (names)` (tag `-- op-dedupe`),
  aliasing exactly the removed names, so no other kernel name becomes visible.
* Fixes by hand (`fixes/`): dot notation `ρ.HasHTWeightsAtSelf` on the kernel's `PkgI4.GaloisRep` written
  `PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := ρ)` (12 places); explicit `_root_.HDec.Y` to removed copies redirected
  to `_root_.Y` (19 lines); `LeafQM.AV.QML3.goodReduction` named in one proof (TailC); a redundant
  `attribute [instance]` line on the old AbVar copy dropped (TailH); 12 `#hdec_same HDec.X` checks whose copy is
  gone replaced by comments (LPrefix). No statement changed, no hypothesis added.

## What remains

* The G9 layer (294 copies): identifying `ZInQ.Contrib.G9.PkgI4` with `PkgI4` (the kernel's G9 states its leaves
  over its own copy) would let them go.
* The leaf-push2 copies inside H (behind r3, r18, r22) and the `G7Data`/`TateBridge35` and `E1Sub.bcPt` variants are
  genuinely different statements from the kernel's; moving them needs a statement-level decision, not a dedupe.
