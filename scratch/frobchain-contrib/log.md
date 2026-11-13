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
