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
- 06:25 DupScan.lean (same type hash, and for defs same value, against every constant of the environment): theta-glue's
  §0 verbatim copies (thetaEight; qmR, ThetaEightSquare, QMThetaSymmetricCurve differ only through those) and
  ThetaGlue.esymm_cons_succ duplicated theta-split's -> `export ThetaSplit (...)`; LinYangPrinted.SpMat = gt-theta's
  GapTheta.Mat4 (Contrib) -> import ThetaModularityM46 and use Mat4; LinYangPrinted.countable_B = the chain's instance
  (TailZ3) -> deleted. Rebuilt OK; DupScan again: no copies left (blkR0..3 in the engine are equal-valued by design).
- 06:40 Dead.lean (closure of frozenTarget + the Route 1 theorems): theta-split §5-§6 (Route 2, CM nodes; 36 decls),
  ThetaGlue.fin2_add_cast, LinYangPrinted.psi4Th_eq/chi10Th_eq unused -> removed. Rebuilt OK (Main + Discharges),
  frozenTarget axioms standard. Module sizes: Kron 51 KB, Split 16 KB, Glue 64 KB, Printed 31 KB.
- 06:55 final checks on f016e90b: PruneScan OpenResearchLeaves21 29, OpenTextbookLeaves11 12, OpenAddedLeaves18 15,
  OpenGlue7 1 = 57 fields, 0 unused, prune set empty. DumpCompact 13876 constants; cmp_hashes (cmp_hashes_out.txt):
  removed 14 (11 pruned projections + 3 dead readers), new 29 (TailK 6: ThetaRatiosAtQM, Jmap_ne_zero + 3 _simp aux,
  thetaPointOfFibre_of_qm_atQM; TailZ41 23: OpenAddedLeaves18 + generated, conversion, open29), changed 254 (216
  generated auxiliaries/projections of the 11 edited bundles, 13 conversions value-only, 23 stack theorems type-only
  (hθ), gluePieces_of_open4, frozenTarget type (l : OpenAddedLeaves18)). No `_proof_N` renumbering.
  frozenTarget's printed type differs only in `OpenAddedLeaves17` -> `OpenAddedLeaves18`.
  DischargesTest: same discharges and controls (t1, t3 flagged sorry), 64 open hypotheses (base 63).
