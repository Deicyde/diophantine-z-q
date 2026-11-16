# pi0-fold results log

- 11-16 00:10 start. Base ec797e65 (wip/leaf-fold30). lean/.lake/build missing: copied from ~/dzq-wt/dcy3-fold (lean/ZInQ identical).
  Tools copied from scratch/dcy3-fold (DumpCompact incl. Contrib.OneProof, PruneScan, DeadCascade, cmp_hashes, prune_lib), paths changed.
- 00:20 **BASE DOES NOT BUILD** (ec797e65 = origin/wip/leaf-fold30 minus its docs-only tip ddbcfd61):
  `lake build +ZInQKernel.OneProof.Main` reports a build cycle TailZ23 -> TailZ40 -> TailZ39 -> ... -> TailZ24 -> TailZ23.
  Cause: module-name collision. rigid-prune's `TailZ40` (0bf41b17, QMFamilyGroupLaw; imported by TailZ23 and by
  Contrib/OneProof/DeligneComponentsY3Used, which TailZ34 imports) was overwritten by leaf-fold30's autofold output
  (56dcca02, persists-dvr, `sixContactMin_of_open34`, imports TailZ39).
  Fix (committed separately, so the integrator can see it): rigid-prune's module restored as TailZ40 verbatim
  (56dcca02^), leaf-fold30's autofold module moved verbatim to the new TailZ60 (the first name of my reserved range),
  Main.lean imports TailZ60. No other file touched (DeligneComponentsY3Used is Contrib, not editable, so TailZ40 has to
  keep rigid-prune's content).
- 00:25 base checks: DumpCompact 17254 constants (hashes_before.txt, dumpcompact_before_out.txt incl. frozenTarget's pp.all
  type), axioms standard. PruneScan base: OpenResearchLeaves26 25, OpenTextbookLeaves11 11, OpenAddedLeaves17 11,
  OpenGlue8 1 = 48 fields, 0 unused (prunescan-base-out.txt). kinds.tsv before: H rows 48, strict 40 LEAF / 8 GLUE,
  strictest 39 / 9; all 59 rows strict 48 / 11, strictest 47 / 12 (kinds-counts-before.txt).
- 00:35 Scope.lean (Scope_out.txt): 47 closure constants read R1R2fpRep or the two fields. Two un-editable Contrib
  files constrain the in-place route: SGRFold (`LeafAdopt.R1R2fp_of_rep (x6Rows_of_open14 ...).1`, so R1R2fp_of_rep
  and x6Rows_of_open14 must switch together) and STQM (`GapST.stQM_of`/`cm_point` take the strong row, and
  `GapST.cmDescends_of` passes it to `LeafQCheck.cmDescends_of`, so that one keeps a strong form).
- step 1 (thread.py; producers.lean pasted into TailZ21; gen_stqmw.py writes the new contributor file
  Contrib/OneProof/Pi0FoldSTQM.lean with GapST.cm_pointW, stQM_ofW): R1R2fpRepW + R1R2fpRepW_of_rep (LPrefix, next to
  R1R2fpRep); R1R2fp_of_rep on the weak row; every consumer binder / internal-bundle field `LeafAdopt.R1R2fpRep` ->
  `R1R2fpRepW` (33 lines), producers' conclusions kept strong; TailO cmDescends_of body -> cmDescends_ofW, strong
  cmDescends_of delegates; cmDescends_of6 uses W; TailX stQM uses stQM_ofW; 3 patterns one conjunct shorter;
  x6ConicModel_of_published wraps R1R2fpRepW_of_rep; x6Rows_of_open14 from x6Rows_of_leavesW (no field read).
- 01:05 step 1 build OK (13695 jobs; one off-chain fix-up in TailZ17 researchLeaves10_of_open11: R1R2fpRepW_of_rep wrap). frozenTarget axioms standard.
- 01:12 PruneScan after step 1: exactly OpenAddedLeaves17.{deligneComponentsX6PrintedAb, geomConnOfAlgClosure} unused; prune set = the two fields in OpenAddedLeaves12-17 (12 entries, prune-set-step1.txt). Top-bundle field statements (used-fields lists) identical to the base.
- 01:20 step 2 (prune_pi0.py, prune_out.txt: 130 deleted lines): 12 fields (2 x OpenAddedLeaves12-17, with docstrings),
  10 assignments, dead readers x6Rows_of_open13, researchLeaves12_of_open13, addedLeaves11_of_open12,
  sixContactMin_of_open16 (TailZ22, with their #print lines). TailZ22 module doc updated. Build OK (13695 jobs),
  frozenTarget axioms standard. kinds.tsv rows (2) and claims.tsv rows (2) deleted (removed-rows.txt).
  kinds after: H rows 46, strict 38 LEAF / 8 GLUE, strictest 37 / 9 (kinds-counts-after.txt).
- 01:25 after step 2: PruneScan 25 + 11 + 9 + 1 = 46 fields, 0 unused, prune set empty (prunescan-out.txt).
  DumpCompact 17276 constants; cmp_hashes_out.txt: removed 16 (12 projections of the pruned fields, 4 dead readers),
  new 38 (helpers: LPrefix 2, TailO 1, TailZ21 33 incl. X6LeavesW's auxiliaries, Pi0FoldSTQM 2), changed 157
  (110 generated auxiliaries/projections of the 18 edited structures; 47 consumers/conversions, listed in the report).
  frozenTarget's pp.all type text identical (binder types keep their names); frozenTarget hash unchanged.
- DischargesTest: t1 discharges OpenGlue8.nvLocalInertia (still assumes it), t2 nothing, t3 cartierSmooth flagged
  sorry; 7 real discharges of existing contributions; 57 open hypotheses. Saved to scratch/contrib-kit/.
- OpenStatements.lean: 57 open hypotheses. render_open.py REFUSED at first: claims.tsv had 4 stale rows for fields that
  earlier folds removed (igusaGL2, h29, elkiesX6StarPrinted, semistablePersistsSHcp; the same failure on the base,
  which is why leaf-fold30's tip ddbcfd61 regenerated only the json). Those rows deleted (rows of removed fields;
  saved in stale-claims-rows-removed.txt), then render_open.py wrote OPEN.md, pages-wanted.md, CONTRIBUTING.md,
  STATUS.md and --check says "ok: 57 open hypotheses, all classified; 4 generated files up to date".
- 01:35 report docs/research/pi0-fold.md written.
- 01:40 .fleet/pi0-fold.md written; done.
