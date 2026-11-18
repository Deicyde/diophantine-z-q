# cm-fold-rebase results log

- 13:17 start. Base 6298e108 (cox-lattice). Merged origin/main 67950e829 (fold-b112 + hygiene; top
  sixContactMin_of_open76, TailZ83, OpenResearchLeaves57) with merge commit d28bdc4e, clean.
- Main's count (docs/one-proof/OPEN.md, kinds.tsv): 29 H rows (27 research + 2 added), strict 5 LEAF / 24 GLUE on 29
  (+ hPC outside H). VERIFIED (read).
- Finding: main's TailZ80 (bost-gr9) is a copy-based reroute: the bundles OpenResearchLeaves53..8EB and the chain
  open8..open72 are copied into HDec.HSyn.GR9 with bostLowerBoundAnSS weakened; open73 = GR9.open72. So cm-branch2's
  R5Prune chain (over the un-weakened bundles, needing bostLowerBoundAnSS) cannot be fed from OpenResearchLeaves57.
  Plan: thread c through GR9.open48 -> GR9.open8 -> (Top2) open7_cm2; dirty-scan that root; copy only the dirty
  declarations not already copied by cm-branch2's R5Prune (reuse its _r5 copies); new generation
  OpenResearchLeaves58CM = 57 - gonzalezRotgerThm512X6RCF + 5 CM fields, conversions 58CM->56_cm->55_cm->54_cm->
  GR9.36EBCF_cm->GR9.35EBCF_cm->GR9.34EBCF_r5 (verbatim copies minus the GR line).
- 14:14 base build (TailZ83, CMBranch.R5Prune, CMBranch2) EXIT 0 (15406 jobs). (First attempt was killed by the
  harness 10-min background limit, restarted.)
- Top3.lean (gen/mk_top3.py: 27 GR9 chain theorems open48 -> open8 with c : CMInputs2 threaded; bottom callee
  cm-branch2's open7_hf_pz_eb_cm2) lake build EXIT 0. VERIFIED.
- Dirty3.lean (roots: GR9.open48_cm2 + GR9 conversions 31<-32<-33<-34<-35): dirty 954 of 65663 (first run with the
  single root missed the 34->31 conversions: 845 of 64946). gen/gen_r5b.py: 191 dirty copies needed, 107 reused
  from cm-branch2's R5Prune (same _r5 names), 84 new (TailZ80 GR9 bundles/conversions/height-row consumer + Top3
  chain), 2878 lines in R5GR9_1.lean, R5GR9.lean; the 3 applicable cm-branch2 patches each applied once.
- gen/gen_open77.py -> Open77.lean: OpenResearchLeaves58CM (57 - gonzalezRotgerThm512X6RCF + 5 CM fields),
  56_cm, 55_cm, 54_cm, GR9.36EBCF_cm, GR9.35EBCF_cm, conversions verbatim minus the field line; top
  sixContactMin_of_open77_cm.
- 14:40 lake build CMFoldRebase.R5GR9, CMFoldRebase.Open77, CMFoldRebase (deliverable) EXIT 0, first try.
  #print axioms sixContactMin_of_open77_cm, sixContactMin_of_open76_cmfold: [propext, Classical.choice, Quot.sound].
  VERIFIED (build2.log).
- 14:31 GRUse77.lean (closure of sixContactMin_of_open77_cm, 130504 constants): R5ptProps, GRDict.r5ptProps_of_thm512,
  GRX6AbPrint.gonzalezRotgerX6Ab_of_print, GRDict.GonzalezRotgerThm512X6, GR512Bridge.* (Thm512X6RCF, _of_rcf),
  GR9.OpenResearchLeaves35/36EBCF.gonzalezRotgerThm512X6, OpenResearchLeaves53/54/57, sixContactMin_of_open4_hf_pz_eb,
  FS5NoCM.R1R2fpFullProps: all ABSENT. CoxProperLattice + coxProperLattice_proof, HeightAdditivityUpper,
  ReducedCMPeriod, the 5 CM statements, GaudronRemondSec9LowerAnSS: present. All 31 fields of OpenResearchLeaves58CM
  are read (projection occurs). VERIFIED (gruse77-out.txt).
- 14:35 lake build ZInQKernel.MainGreenTao (worktree's lean/ ZInQ package was not built), then OneProof.Main +
  Discharges EXIT 0. MainDryRun.lean (Main.lean with r : OpenResearchLeaves58CM and sixContactMin_of_open77_cm r t l):
  EXIT 0, 'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]. VERIFIED.
- 14:40 #discharges (Discharges.lean: Main, Discharges, CMFoldRebase): "30 open hypotheses, 13341 theorems checked,
  315 discharge one" = 15 pre-existing reductions (carayol, ds965, deRham x2, javanpeykar, the two X6 rows, deligne,
  gaudronRemond sec9 from Bost, pazuki x4, hodgeTate x2) + 300 projections X_r5.<field> / X_cm.<field> of copied
  bundle structures (known noise). No field discharged by this task (expected: the removed field is unread, not proved).
- No existing ZInQKernel file modified (git diff --diff-filter=MD origin/main -- ZInQKernel empty).
