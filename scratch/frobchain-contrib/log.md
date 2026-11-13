# frobchain-contrib results log

## Setup (2026-11-13)
- Worktree at fork main 83651ea9; merged origin/wip/linked-frob (795a9bd9) and origin/wip/frob-contrib
  (8b220e14, which has ZInQKernel/Contrib/AbsFrob/ and Contrib/UnramRoots/). origin/wip/alg-frob-red is not
  ahead of fork main (0 commits). VERIFIED (git).
- Source identity (cmp, VERIFIED): unram-tate TateBridge.lean = frob-trace part_tate_src.lean; g14-trace
  part_bridge.lean = frob-trace part_bridge_src.lean; g14-trace part_g14.lean = frob-trace part_g14_g14.lean;
  frob-trace part_frob.lean = alg-frob-red src_part_frob.lean; mul-rigidity Rigidity.lean = alg-frob-red
  src_Rigidity.lean; alg-frob-red AlgFrobRed.lean = frob-pieces src_AlgFrobRed.lean.
- alg-frob-red part_red.lean lines 1363-1373 (`def AlgFrobRedRed.AbsFrob` + docstring) occur verbatim in
  ZInQKernel/Contrib/AbsFrob/AlgFrobRed.lean (frob-contrib). VERIFIED (generator assertion).
- Contrib/AbVarBC/Points.lean holds unram-tate's BCPoints in namespace ZInQ.Contrib.AbVarBC, so no clash with
  TateBridge.lean's UnramTate BCPoints block. VERIFIED (read).

## Step 2 plan: modules (generator scratch/frobchain-contrib/build_modules.py)
TateBridge, Bridge35, FrobTrace, Rigidity, AlgFrobRed, FExtend, Pieces, LinkedStatement, LinkedFrob, Main.

## Step 2 compile outcomes (VERIFIED, lake build, this host)
- TateBridge: exit 0 (103 s; only this module rebuilt, 9199 jobs).
- Run chain1: Rigidity, Bridge35, FrobTrace, AlgFrobRed (42 s), FExtend, Pieces built; LinkedStatement failed:
  `GaloisCopy` is `G0ModField.GaloisCopy` (nested namespace). Fixed context line to `open PkgI3 G0ModField.GaloisCopy GlueC10Link`.
- Run chain2: LinkedFrob failed (`Add (PtQ L A)`, `tmOf_eq` unknown): without ModField's file-level opens, `GQ` auto-bound
  as an implicit variable. Fixed by putting the two ModField `open` lines before parts/10 (as in linked-frob's file).
- Run chain3: LinkedFrob exit 0. Run main1: Main exit 0. All 10 modules build, no `sorry` warnings.

## Step 3: Check.lean (VERIFIED)
- scratch/frobchain-contrib/Check.lean = scratch/contrib-check/Check.lean + `import ZInQKernel.Contrib.FrobChain.Main`
  + `#check`s (the chain's statements elaborate as `Prop`, no auto-bound arguments) + 32 `#print axioms` lines.
- First run: missing olean ZInQ.PoleValuation; `lake build` of Check's 21 imports: exit 0, 388 s (11655 jobs).
- `lake env lean scratch/frobchain-contrib/Check.lean`: exit 0 in 7 s, no error; 48 axiom reports (16 contrib-check
  + 32 frob chain), all [propext, Classical.choice, Quot.sound] (4 line-wrapped). Output: Check.out.
- No import clash between the FrobChain modules and the contrib-check modules (same file imports both).

## Audits (VERIFIED)
- AxiomAudit.lean (metaprogram over all constants whose module is ZInQKernel.Contrib.FrobChain.*): exit 0 in 185 s;
  "FrobChain declarations: 572 (theorems: 464); with non-standard axioms: 0 []". Output AxiomAudit.out.
- verbatim_check.py: all 18 source slices occur verbatim in their modules (trailing blank lines aside); the dropped
  `def AbsFrob` block equals frob-contrib's; ALL OK. Each chain Prop is defined once, except the two known pairs
  FrobTraceLink (G14Bridge copy / G14Trace) and SmoothGeomConnIntegral (AlgFrobRedRed / FrobPieces), both shown
  equal by Iff.rfl in Main.lean. Output verbatim_check.out.
- Not found in the worktree (grep over ZInQKernel/ and scratch/): any theorem whose type is PkgI2.ReductionTorsionBijective,
  PkgI2.NeronMappingAbelianScheme or PkgI3.TateModuleFree; h-decomposition.md lists T3, T4 as "open". They stay hypotheses.
