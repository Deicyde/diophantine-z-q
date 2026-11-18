# y3-x6b log

## 2026-11-17
- Base: wip/y3-x6b = origin/wip/cm-fold-rebase 664e00417 + origin/wip/y3-p1j d1eb63916. Top here:
  `HDec.HSyn.sixContactMin_of_open77_cm (r : OpenResearchLeaves58CM) t l` (CMFoldRebase/Open77.lean).
- Step 1: checked out from origin/wip/y3-x6 (e9c0d2dd7): ZInQKernel/Contrib/OneProof/Y3X6/, Y3X6Fold.lean,
  scratch/y3-x6/, docs/research/y3-x6.md, .fleet/y3-x6.md (y3-x6's own files only; no cm-branch / cm-branch2 content).
  Generators copied to scratch/y3-x6b/gen/ for adaptation.
- Step 2 (VERIFIED, lake build ZInQKernel.Contrib.OneProof.Y3X6Fold, EXIT 0, 15415 jobs, first try; scratch/y3-x6b/build1.log): gen_y3b.py -> Y3X6/Copy1-5.lean (244 blocks from CMBranch/R5Prune*.lean + CMFoldRebase/R5GR9*.lean; GR9 copies of the x6Rows/openGlue7 patches added; GR9.SGRFold.heckeSqrtBranchAny_of_open29 and GR9 conversion 35->34 deleted); gen_top_b.py -> Y3X6/Top.lean (from CMFoldRebase/Open77.lean): top HDec.HSyn.sixContactMin_of_open78_y3x6 (r : OpenResearchLeaves59Y3) t l, axioms [propext, Classical.choice, Quot.sound]. Base.lean dropped (Row.lean imports CMFoldRebase.Top3 + Y3ToP1j directly; Top2 compiles on this base).
- Axioms (VERIFIED, scratch/y3-x6b/axioms.txt): sixContactMin_of_open78_y3x6, sixContactMin_y3x6b, the Row theorems,
  GapST.cm_pointW_y3: [propext, Classical.choice, Quot.sound].
- Closure scan (VERIFIED, scratch/y3-x6b/Closure.lean -> closure.txt; 129961 constants): X6Props, R2X6Props, CMExists,
  X6Surj, R2X6PropsIff, R5ptProps, X6CoarseModuliIdeal, ElkiesX6StarEveryIdeal, X6CoarseModuli, ElkiesX6StarEvery,
  ElkiesX6StarPrinted, ElkiesX6StarFunctionField, ElkiesEquationsX6Ab, BabaGranathRationalAb, GonzalezRotgerX6Ab_r5,
  gonzalezRotgerX6Ab_r5_of_coarse, x6ModuliWitness_of_coarse, SGRDirect.elkies_coordinate, GR9.SGRFold.heckeSqrtBranchAny_of_open29,
  R1R2fpRepW(_r5), R1R2fp, X6ConicModel, OpenResearchLeaves57: not in the closure. Y3ToP1j, HeckeSqrtBranchAny, R1R2fpY3,
  OpenResearchLeaves59Y3.{y3ToP1j,heckeSqrtBranchAny}: in. Constants with suffix _r5/_cm: 3, all unrelated lemma names
  (RayClassCFT.nrd_pos_of_cm, GapST.twist_of_cm, GlueAssembly.max_one_hA_le_cm); no cm-branch2/cm-fold-rebase copy.
- Reader grep (VERIFIED, scratch/y3-x6b/grep-x6.txt). Readers NEW on this base (not on cm-branch2's route), all re-sourced:
  Open77 conversions 36EBCF_cm_of_54_cm (x6CoarseModuli_of_ideal, elkiesX6StarEvery_of_ideal') and 34_r5_of_35_cm
  (gonzalezRotgerX6Ab_r5_of_coarse, elkiesX6StarFunctionField_of_every + x6ModuliWitness_of_coarse) -> y3row := y3ToP1j,
  heckeSqrtY3 := heckeSqrtBranchAny (Top.lean); GR9.x6Rows_of_open14_hf_gm_pz_eb_r5 -> patched to r1r2fpY3_of;
  GR9.SGRFold.heckeSqrtBranchAny_of_open29_r5 -> deleted, GR9.openGlue7_of_OpenGlue8_r5 patched to r.heckeSqrtY3;
  GR9.openResearchLeaves34_of_35_eb_cf_r5 (unused on the route) deleted; GR9 bundle conversions (elkiesEquationsX6Ab_of_printed,
  babaGranath, Elkies fields) by field_ops; GR9 bundles 9EB/8EB field r1r2 : R1R2fpRepW_y3 = Y3X6.R1R2fpY3. None blocked.
  Y3X6/* and Y3X6Fold.lean: no code line mentions an X6 field or clause name.
- lake build ZInQKernel.OneProof.Main, Discharges, MainGreenTao, DeRhamRange: EXIT 0, 15987 jobs (build-main.log).
- Dry-run fold (VERIFIED, scratch/y3-x6b/MainDryRun.lean -> maindryrun-out.txt): main's Main.lean with research bundle
  OpenResearchLeaves59Y3 and H argument sixContactMin_of_open78_y3x6 r t l; EXIT 0; frozenTarget axioms
  [propext, Classical.choice, Quot.sound].
- #discharges (VERIFIED, scratch/y3-x6b/discharges.txt): "30 open hypotheses, 14230 theorems checked, 405 discharge one"
  (against main's OpenResearchLeaves57); 15 pre-existing reductions (same as cm-fold-rebase), 390 projections of copied
  structures (300 _r5/_cm as in cm-fold-rebase + 90 _y3/_y3x6/59Y3); none from y3-x6b; no sorry.
- Count (kinds.tsv rule): 5 LEAF / 28 GLUE on 33 -> 5 LEAF / 28 GLUE on 33; GLUE change 0 (strict and strictest).
- Deliverables: scratch/y3-x6b/autofold.json, kinds-rows.tsv, kinds-remove.tsv; report docs/research/y3-x6b.md.
