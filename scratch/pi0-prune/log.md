# pi0-prune results log (base 43513d87)

## Scope (VERIFIED, compiled probes)
- `Scope.lean` → Scope_out.txt: tainted structures (carry `R1R2fpRep`): ResearchLeaves3, OpenResearchLeaves2/5/7/8/9;
  57 live constants mention them or `R1R2fpRep` in their type.
- `Reach.lean` → Reach_out.txt: live readers of the projections `OpenAddedLeaves12..17.{deligneComponentsX6PrintedAb,
  geomConnOfAlgClosure}`: 23 constants (x6Rows_of_open14 … sixContactMin_of_open29, the addedLeaves conversions).
- `Copy.lean` → Copy_out.txt: the copy set = tainted-type ∪ readers ∪ everything above them in the closure:
  80 constants (incl. frozenTarget) + 6 structures. Line ranges at base 43513d87.

## Build
- Generator scratch/pi0-prune/tools/gen.py (+ cfg_*.py, common.py): copies declarations by line range keeping the
  source file's namespace/section/open skeleton; renames (suffix W; OpenAddedLeaves12..17 → …P; R1R2fpRep → R1R2fpRepW).
- Pi0Prune/Base.lean: R1R2fpRepW, R1R2fpRepW_of_rep, R1R2fp_of_repW, producers (CoarseX6OfFineW, CanonicalCoarseX6W,
  GeomConnX6W, geomConnX6W_of_gr, r1r2fpRep_of_printedW, r1r2_of_publishedW, x6Rows_of_leavesW) and copied
  destructurers/consumers. COMPILED (lake env lean, 8 s) after 3 pattern fixes (one conjunct fewer in r1rec_of_rep,
  r5fp_of_rep, pairsLift_of_rep).
- Pi0Prune/Old.lean (6 W bundles + 37 copied decls) COMPILED first try; Pi0Prune/Upper.lean (OpenAddedLeaves12P..17P,
  conversions, x6Rows_of_open14W, open17W..open29W) COMPILED first try.
- Pi0Prune.lean: openAddedLeaves17P_of, sixContactMin_of_open29P, sixContactMin_of_open29_pruned.
  `lake build ZInQKernel.Contrib.OneProof.Pi0Prune` OK; #print axioms of r1r2_of_publishedW, sixContactMin_of_open29P,
  sixContactMin_of_open29_pruned: [propext, Classical.choice, Quot.sound] (VERIFIED).
- ClosureCheck.lean (VERIFIED, compiled): closures of sixContactMin_of_open29_pruned (217,052 constants) and
  sixContactMin_of_open29P contain no projection `*.deligneComponentsX6PrintedAb` / `*.geomConnOfAlgClosure`, no
  DeligneComponentsX6Printed(Ab), GeomConnOfAlgClosure, R1pi0Props, R1R2fpRep, r1r2_of_published,
  sixContactMin_of_open17/29. frozenTarget_pruned (frozenTarget's statement, via _pruned) and frozenTarget_P (over
  OpenAddedLeaves17P) compile; axioms [propext, Classical.choice, Quot.sound].
- PruneScanPi0.lean (r6-nf's PruneScan rooted at frozenTarget_pruned; 2 min 13 s): OpenResearchLeaves22 0/29 unused,
  OpenTextbookLeaves11 0/12, OpenAddedLeaves17 2/14 unused [deligneComponentsX6PrintedAb, geomConnOfAlgClosure],
  OpenGlue7 0/1; prune set = exactly those 2 FIELD lines (prune-set.txt). VERIFIED.
- #discharges (discharges.txt): 63 open hypotheses, 2129 theorems, 123 lines. 116 are auto-generated projections of the
  copied structures (…W / …P) whose "still assumes" is the copied bundle itself: not discharges. The other 7 are the
  pre-existing contributions. Pi0Prune discharges no field (expected: it is a prune, not a proof of a field).
