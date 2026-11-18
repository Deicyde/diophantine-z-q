# fold-c8: replaying the joint C8 fold on a later head

The fold is one generator run. The Contrib proof files are separate from it (they come with the merges), so a
replay is: merge, build, taint, generate, build, check.

1. Merge the components (both merged cleanly on wip/leaf-fold33b b9b85486):

       git merge origin/wip/conrad-b3      # e579047cc: c8-conrad3 (7289ef659), c8-conrad2, ht-merge (027f637cd), derham-scholze, ht-abvar
       git merge 8050603b                  # PR #86 head: CloudR2Poincare.FinalUnconditional.poincareComplement_proof

   Hygiene: rename the dry-run scratch files that declare HDec.HSyn bundles to `.lean.txt` (list in log.md §1;
   commit 90e65c77 here). If the head already has these merges, skip this step.
2. Build (PR #86's `ResidueFieldModels` alone takes about 35 min):

       lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.C8Printed \
         ZInQKernel.Contrib.OneProof.ScholzeH1AbVar ZInQKernel.Contrib.CloudR2Poincare.FinalUnconditional
3. Taint on the head's Main (c8-conrad2's seeds; about 2 min):

       lake env lean scratch/fold-c8/gen/Taint.lean > scratch/fold-c8/gen/taint_out.txt
4. Generate (`--dry-run` first: it writes only `scratch/fold-c8/gen/*-dryrun.lean.txt` and prints the count):

       python3 scratch/fold-c8/fold_c8.py --dry-run
       python3 scratch/fold-c8/fold_c8.py

   The script reads the head's Main (top `sixContactMin_of_open<N>`, bundles) and refuses to run (with a message) if:
   * the textbook bundle is not the empty `OpenTextbookLeaves18`;
   * the added bundle is not exactly `{picRepresentableAbVar, kleimanPicZeroProper954SiteQ}` (an autofold that
     added an added-bundle field needs a hand edit: that field would have to be carried into the new added bundle);
   * the research bundle has no `hodgeTateDecompOr`;
   * a top above `sixContactMin_of_open79` is not a research-only autofold top
     (`sixContactMin_of_open<k> (r : R) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) := sixContactMin_of_open<k-1> (conv r) t l`);
     such tops are copied automatically (`sixContactMin_of_open<k>_hm`);
   * the chain open79 → open78 → `sixContactMin_of_open73_sf_u` → `GR9.sixContactMin_of_open72_sf_u` changed, or one
     of the edited D2A6Chain declarations (consumer (iii) `openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u`,
     `sixContactMin_of_open45_pz_eb_sf_u`, `sixContactMin_of_open72_sf_u`) has a different text; in that case
     regenerate the top section by hand from the live declarations (the edits are listed in the script).
   It writes `OneProof/H/C8Chain.lean`, the first free `OneProof/H/TailZ<j>.lean` (the next numeric bundle names and
   `sixContactMin_of_open<N+1>`), switches Main.lean (import, binders, call, one paragraph) and replaces the kinds.tsv
   rows (flags as in the specs, session names replaced). It never writes claims.tsv or volatile.tsv.
5. Build and check:

       lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.C8Chain ZInQKernel.OneProof.H.TailZ<j>
       bash scratch/fold-c8/run_checks.sh 1 hashes_fold0.txt   # after a base DumpCompact into /tmp/fc8/hashes_fold0.txt

   Edit the bundle names in `scratch/fold-c8/FoldCheck.lean` (field check, checked names) if the numbers moved.
   Then `python3 scripts/one_proof/render_open.py` and `--check`.
