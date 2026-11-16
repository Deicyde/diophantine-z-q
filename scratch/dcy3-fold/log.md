# dcy3-fold results log

- 11-15 23:00 start. Base 094bdd96 (wip/leaf-fold29). origin/wip/dcy3-used (36240662) already an ancestor of the base
  (DeligneComponentsY3Used.lean present, not yet imported by the chain).
  lean/.lake/build was missing: copied from ~/dzq-wt/r6-nf (lean/ identical). Base build rebuilds part of the tree.
- Tools copied from scratch/r6-nf (PruneScan, DeadCascade, DumpCompact incl. Contrib.OneProof, cmp_hashes, prune_lib),
  paths changed to scratch/dcy3-fold/.
- 11-15 23:29 **BASE DOES NOT BUILD.** `lake build +ZInQKernel.OneProof.Main` on 094bdd96: every module up to
  TailZ37 and the Contrib modules build, but ZInQKernel/OneProof/Main.lean fails: `Unknown identifier
  H29Split.LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZLemma29PrintedNe3`, `TYZThm21At31`,
  `tyzLemma29Mod2_of_sixLeaves` (Main.lean:66-75). Cause: leaf-fold29 (3b2562f1) hand-folded h29-ne3 into Main but did
  not copy h29-ne3's drop-in scratch/h29-ne3/TYZLemma29Mod2.lean over ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean
  (the tree still has h29-fix's version). origin/wip/leaf-fold29's tip 305280f7 changes only docs.
  Workaround for this task's checks: the drop-in is copied into the working tree LOCALLY ONLY and is never committed
  (that Contrib file is outside this task's allowed edits). The integrator must apply it to leaf-fold29.
- 23:31 base + drop-in (local): `lake build +ZInQKernel.OneProof.Main` OK (13685 jobs); frozenTarget axioms standard.
- 23:32 base DumpCompact (OneProof + Contrib.OneProof modules): 16935 constants -> hashes_before.txt; frozenTarget's
  pp.all type in frozenTarget_before.txt.
- 23:37 base PruneScan: OpenResearchLeaves24 26, OpenTextbookLeaves11 11, OpenAddedLeaves17 13, OpenGlue7 1 = 51 fields,
  0 unused (prunescan-base-out.txt, used-fields-base.txt, unused-all-base.txt, prune-set-base.txt).
  kinds.tsv before (kinds-counts-before.txt): H rows 51, strict 41 LEAF / 10 GLUE, strictest 39 / 12; all 62 rows strict
  49 / 13, strictest 47 / 15. The field's row: added, GLUE / GLUE.
- 23:41 step 1 (thread.py: hY3 binder on addedLeaves8_of_open9, open11-open27; supplied in open28 by DCY3Used.y3Connected_of_leaves; TailZ34 imports DeligneComponentsY3Used): build OK first try (13686 jobs), frozenTarget axioms standard.
- 23:45 PruneScan after step 1 (prunescan-step1-out.txt): exactly OpenAddedLeaves17.deligneComponentsY3PrintedAb unused;
  prune set (prune-set-step1.txt) = OpenAddedLeaves9.deligneComponentsY3Printed and the Ab field in OpenAddedLeaves12-17.
  The off-chain generations OpenAddedLeaves10 (TailZ17) and 11 (TailZ18) must lose the field too: addedLeaves10_of_open11
  and addedLeaves11_of_open12 fill them from the next generation (prune-set-applied.txt = scan set + these two).
  DeadCascade (dead-cascade.txt): only generated casesOn/recOn and the off-chain conversions addedLeaves9_of_open10,
  addedLeaves10_of_open11, addedLeaves11_of_open12 with open13-16 above them; these only lose an assignment, so no
  declaration is deleted.
- step 2 (prune_dcy3.py, prune_out.txt: 52 deleted lines): 9 fields (with docstrings) and 9 assignments. Docstrings of
  addedLeaves8_of_open9, OpenAddedLeaves9, sixContactMin_of_open28 and Main's module doc updated.
  kinds.tsv and claims.tsv rows of deligneComponentsY3PrintedAb deleted (removed-rows.txt).
- 23:52 build after step 2: OK (13686 jobs); frozenTarget axioms standard.
