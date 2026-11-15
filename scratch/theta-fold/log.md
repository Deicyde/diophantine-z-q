# theta-fold results log

- 11-15 04:12 start. Base a47f9162 (leaf-fold23, frozenTarget through sixContactMin_of_open28). linyang-printed's
  three Lean files copied to scratch/theta-fold/src/ (read-only references; not committed to the tree as modules).
- Plan: thetaRatiosAlgebraic is read only by TailK's gluePieces_of_open4 (via thetaPointOfFibre_of_qm_ratios);
  TailO's L2595/L2625 and every other occurrence are bundle-to-bundle conversions. ThetaRatiosAlgebraic (universal,
  every abelian surface over a number field) does not follow from the two printed leaves, which give only
  theta-split's use form ThetaRatiosAtQM (QM curve Ω(τ)). So: move ThetaRatiosAtQM and thetaPointOfFibre_of_qm_atQM
  (theta-split, unchanged) into TailK, give gluePieces_of_open4 the binder
  `hθ : PkgI1.QMHauptmodul → ThetaSplit.ThetaRatiosAtQM` (fed with l.qmHauptmodul), thread hθ through
  sixContactMin_of_open4 .. open28 (as yu-prune threaded hYu), supply it in a new top open29 (TailZ41) from
  igusaThetaExpressions and linYangEx29All via the contributor modules; then PruneScan + prune thetaRatiosAlgebraic.
- 04:50 base build `lake build +ZInQKernel.OneProof.Main` OK (12986 jobs, build tree in the worktree was stale at TailZ34;
  started with a shell `&`, one process only); frozenTarget axioms standard. DumpCompact (tools copied from
  scratch/yu-prune/ with paths into scratch/theta-fold/): 13861 constants -> hashes_before.txt,
  frozenTarget_before.txt. PruneScan base: OpenResearchLeaves21 29, OpenTextbookLeaves11 12, OpenAddedLeaves17 14,
  OpenGlue7 1 = 56 fields, 0 unused (*-base.txt).
- 05:30 step 1 (plumb.py: ThetaRatiosAtQM + thetaPointOfFibre_of_qm_atQM moved into TailK, hθ binder on
  gluePieces_of_open4 and sixContactMin_of_open4/6..28; mk_modules.py: Contrib/OneProof/LinYang{Kron,Split,Glue,Printed};
  TailZ41: OpenAddedLeaves18 = OpenAddedLeaves17 + igusaThetaExpressions + linYangEx29All, open29; Main switched)
  compiled first try: `lake build +ZInQKernel.OneProof.Main` OK (12991 jobs; LinYangGlue 109 s), frozenTarget axioms
  standard. kinds.tsv: thetaRatiosAlgebraic row deleted, two rows added; claims.tsv: thetaRatiosAlgebraic row deleted.
- 05:40 PruneScan after step 1: exactly OpenAddedLeaves18.thetaRatiosAlgebraic UNUSED; prune set 12 fields
  (OpenAddedLeaves4/6/7/8/9/12/13/14/15/16/17/18.thetaRatiosAlgebraic), no constants (prune-set-step1.txt).
  DeadCascade: addedLeaves5_of_open6 (TailO), addedLeaves11_of_open12, sixContactMin_of_open16 (TailZ22) + casesOn/recOn.
- 06:05 step 2 (prune_edit.py; every deleted line in prune_edit_out.txt): 12 fields, 13 assignments, the element in
  openAddedLeaves4_of_Q5's anonymous constructor, 3 dead readers + #print lines. `lake build +ZInQKernel.OneProof.Main
  +ZInQKernel.OneProof.Discharges` OK (12992 jobs); frozenTarget axioms standard.
