# yu-prune results log

- 11-15 02:10 start. Base 688b450d. Build tree copied (reflink) from ~/dzq-wt/gt-qm (.lake/build, lean/.lake).
  Tools copied to scratch/yu-prune/ (PruneScan from scratch/one-proof, PruneScanDead = sem-prune's variant,
  DeadCascade, prune_edit.py, cmp_hashes.py, DumpCompact) with output paths in scratch/yu-prune/.
- 02:14 **Base does not build at TailZ32** (VERIFIED): `lake build +ZInQKernel.OneProof.Main` fails with
  `TailZ32.lean:1:0: import ZInQKernel.Contrib.MulEtale.Direct.Original.StacksCore.Tactic.EgaSgaAttribute failed,
  environment already contains 'Stacks.EgaSga.instInhabitedWork.default' from
  ZInQKernel.Contrib.CloudW01Spread.StacksCore.Tactic.EgaSgaAttribute`. The two files are the same Stacks port
  (only the header comment differs); TailZ31's closure has the CloudW01Spread copy and leaf-fold19's MulEtale wrapper
  the MulEtale/Direct/Original copy. So TailZ32 and Main.lean fail on 688b450d itself; everything up to TailZ31 builds.
  Fixing it needs a Contrib edit (not allowed here). Workaround for the checks: variants of the tools rooted at
  `HDec.HSyn.sixContactMin_of_open25` (TailZ31): DumpCompact31.lean, PruneScan31.lean, DeadCascade31.lean.
- 02:15 base DumpCompact31: 13599 constants (OneProof modules + QMLattice), hashes_before31.txt;
  axioms of open25 = propext, Classical.choice, Quot.sound.
- 02:17 base PruneScan31 (root open25): OpenResearchLeaves19 30, OpenTextbookLeaves10 14, OpenAddedLeaves16 14,
  OpenGlue7 1 = 59 fields, 0 unused (frozenTarget itself has 58: OTL11 drops mulEtaleAbelianScheme). *-base.txt.
- 02:38 step 1 (plumbing, scratch/yu-prune/plumb.py) compiled first try: `lake build ZInQKernel.OneProof.H.TailZ31`
  OK (12139 jobs); open25 axioms standard.
- 02:41 PruneScan31 after step 1: exactly `OpenTextbookLeaves10.yuThm11` UNUSED; prune set 9 fields
  (TextbookLeaves.t27, OpenTextbookLeaves2/3/4/6.t27, OpenTextbookLeaves7/8/9/10.yuThm11), no constants
  (prune-set-step1.txt). Plus OpenTextbookLeaves11.yuThm11 (TailZ32), which the open25 root cannot see.
- 02:43 DeadCascade31: dead readers fibreComTrivial_of_gp3, fibreSimple_of_gp3, gluePieces_of_gluePieces3 (TailD),
  gluePieces_of_open2 (TailE), gluePieces_of_open3 (TailI) + generated casesOn/recOn (dead-cascade.txt).
- 02:50 merged origin/wip/leaf-fold19 (c2ad4181): 495ca918 fixes the TailZ32 import clash (the vendored StacksCore
  attribute modules import CloudW01Spread's). No OneProof/H change in the merge.
- 03:05 step 2 build: TailZ31 OK; then `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` OK
  (12979 jobs); `#print axioms ZInQ.OneProof.frozenTarget` = [propext, Classical.choice, Quot.sound].
- 03:08 PruneScan (Main root): OpenResearchLeaves19 30, OpenTextbookLeaves11 12, OpenAddedLeaves16 14, OpenGlue7 1
  = 57 fields, 0 unused, prune set empty.
- 03:09 DumpCompact (Main, + QMLattice) 13746 constants -> hashes_after.txt; DumpCompact31 13585 -> hashes_after31.txt;
  cmp_hashes.py 31: removed 16 (9 pruned projections + 5 dead readers + 2 aux `_proof_N`), new 2
  (YuB6Emb._proof_1/2), changed 189 (cmp_hashes_out31.txt). YuB6Alg: same type and value hash, module QMLattice ->
  TailA; yuB6Alg_of, yuB6Alg_of', yuB6Alg_of_yuThm11 unchanged.
- 03:25 base worktree (git worktree at c2ad4181, outside this repo dir; build copied from gt-qm) built Main:
  DumpCompact 13761 constants (hashes_before.txt), PruneScan 0 unused of 58.
- 03:35 cmp_hashes.py (Main level): removed 17, new 2, changed 198; classify.py sorts them (classify_out.txt).
  CanonHash.lean in both trees: the 41 unexpected value changes are auxiliary `_proof_N` sharing/renumbering
  (canonical hashes equal).
- 03:40 DischargesTest: same discharges/controls, 64 open hypotheses (was 65). OpenStatements: 64; render_open:
  57 H, strictest 43/14; --check ok.
