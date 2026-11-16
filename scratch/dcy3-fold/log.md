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
- 23:55 PruneScan after (prunescan-after-out.txt): OpenResearchLeaves24 26, OpenTextbookLeaves11 11, OpenAddedLeaves17 12,
  OpenGlue7 1 = 50 fields, 0 unused, prune set empty.
- DumpCompact after: 17037 constants (hashes_after.txt); frozenTarget's pp.all type identical to the base
  (frozenTarget_before.txt vs frozenTarget_after.txt). cmp_hashes_out.txt: removed 9 (the 9 pruned projections), new 111
  (all ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used, now in Main's closure via TailZ34), changed 106: bundle
  auxiliaries of OpenAddedLeaves9-17 (mk, mk._flat_ctor, rec, recOn, casesOn: type; projections after the deleted field:
  value), conversions (value: addedLeaves9_of_open10/_open14, addedLeaves10_of_open11, addedLeaves11_of_open12,
  addedLeaves12_of_open13, openAddedLeaves13..16_of_..; type: addedLeaves8_of_open9, the binder), sixContactMin_of_open11-27
  (type, the binder), sixContactMin_of_open28 (value). open29-31 and frozenTarget: unchanged hashes.
- DischargesTest: same 8 discharges and controls (t1, t3 as before); 61 open hypotheses (base 62). The saved output
  was stale (OpenResearchLeaves23); now OpenResearchLeaves24.
- Docs: OpenStatements.lean wrote open-statements.json, 61 open hypotheses. **render_open.py FAILS on this base,
  independently of this task**: kinds.tsv keys the six h29-ne3 frozenTarget rows by leaf name (tyzLemma29PrintedNe3,
  tyzThm21At31, tyzProp23Printed, tyzTestVectorExists, legendreThreeSquares, jonesPallX2Y2Z16), while Main.lean's
  binders are hL29, hT21, hP23, hfx, hL3s, hJP (leaf-fold29 3b2562f1). Fixing those rows is outside this task's allowed
  edits, so OPEN.md, pages-wanted.md, CONTRIBUTING.md, STATUS.md are NOT regenerated in the repository. Verification in
  a temporary copy with the six keys renamed to the binder names: render_open.py "50 H hypotheses, strictest 39/11,
  11 others"; --check "ok: 61 open hypotheses, all classified; 4 generated files up to date".
  (The committed generated docs were already stale at the base: STATUS.md said 55 H hypotheses, OpenResearchLeaves23.)
- 00:00 report written; local drop-in reverted (working tree clean).
