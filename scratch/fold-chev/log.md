# fold-chev log

Base wip/leaf-fold33b 1a3bab4a (H top `HDec.HSyn.sixContactMin_of_open64`, TailZ71, `OpenResearchLeaves45`).

1. Merged origin/wip/chevalley-free 81ca42f6 (its base fe2f0d4a is an ancestor of the base; no conflicts).
   Hygiene: `scratch/chevalley-free/ChevFree.lean` copied verbatim to `ZInQKernel/Contrib/OneProof/ChevalleyFree.lean`,
   scratch copy renamed `.lean.txt`; `fold/MainCheck.lean` (redeclares HDec.HSyn bundles) renamed `.lean.txt`.
   No host paths in the merged files (grep). Vendored CloudW07 LICENSE/NOTICE already in the base, unchanged.
2. Generator `scratch/fold-chev/gen/gen_bypass.py` (adapts chevalley-free's gen_bypass.py to any head: follows Main's
   top theorem down its chain until the first callee whose research bundle has no `chevalleyPerfect`, composing the
   conversions field by field, readers rerouted to `ZInQ.ChevFree.*`). Dry run on 1a3bab4a: chain
   `sixContactMin_of_open64 -> 63 -> 62 -> 61_k954 -> ... -> 56_k954 -> 55_eb_k954 -> 54_eb_k954 -> 53_eb_k954`;
   `OpenResearchLeaves45` (31 fields) -> `OpenResearchLeaves46` (30); stop bundle `OpenResearchLeaves36EB` (27
   fields); readers bostLowerBound, gaudronRemondThm14, javanpeykarBound. autofold not applicable (needs a proof of
   `ChevalleyPerfect` itself; readers are 9 conversions below the top). kinds.tsv count (autofold's `counts`):
   strict 9/25 on 34 -> 9/24 on 33; strictest 9/25 -> 9/24. claims.tsv has no chevalleyPerfect row (unchanged).
3. Base build `lake build ZInQKernel.OneProof.Main` (16092 jobs, full rebuild of the copied tree, ~2 h; first
   background run stopped at its time limit, rerun completed): frozenTarget standard axioms. Base hash dump
   `scratch/fold-chev/hashes_before.txt` (17348 constants).
4. Fold written: `python3 scratch/fold-chev/gen/gen_bypass.py` -> `ZInQKernel/OneProof/H/TailZ72.lean`
   (`OpenResearchLeaves46`, `openResearchLeaves36EB_of_OpenResearchLeaves46`, `sixContactMin_of_open65`; copy
   `scratch/fold-chev/TailZ72.lean.txt`), Main switched (import, bundle, top, docstring paragraph), kinds row dropped.
5. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
   ZInQKernel.Contrib.OneProof.ChevalleyFree ZInQKernel.OneProof.H.TailZ72` ok (16095 jobs; excerpt `build_fold_excerpt.txt`, full log left out);
   `sixContactMin_of_open65` and `ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound];
   ChevalleyFree's 22 `#print axioms` lines all standard.
6. Hash guard (VERIFIED, `DumpCompact.lean` -> `hashes_before.txt` / `hashes_after.txt`, `cmp_hashes.py`):
   before 17348, after 17386, only before 0, only after 38 (all in `ZInQKernel.OneProof.H.TailZ72`), changed 1
   (`ZInQ.OneProof.frozenTarget`).
7. Closure check (VERIFIED, `FoldCheck.lean`, output `FoldCheck-output.txt`): closure of `ZInQ.OneProof.frozenTarget`
   (302580 constants) contains none of `ZInQ.SemiAbDescend.ChevalleyPerfect`, `semiAbelianDescendsPerfect_of_chevalley`,
   `bostLowerBound_of_printed_chevalley`, `gaudronRemondThm14_of_printed_chevalley`, `sorryAx`, `OpenResearchLeaves45`,
   `sixContactMin_of_open64`; it contains `ZInQ.HeightFix.SemiAbelianDescendsPerfect` and
   `ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`.
8. `lake env lean scripts/one_proof/OpenStatements.lean`: 38 open hypotheses (was 39). render_open.py: 33 H
   hypotheses, strictest 9/24, 5 others (was 34 H, 9/25); `--check` ok. DischargesTest rerun (output copied to
   `scratch/contrib-kit/DischargesTest-output.txt` and here; diff vs. the old output: only `OpenResearchLeaves45` ->
   `46` labels plus the new `ZInQ.ChevFree.pazukiCor13Upper_of_printed_free` row, standard axioms), render_open rerun
   (CONTRIBUTING.md worked example), `--check` ok. frontier_crosswalk.py: tsv unchanged (232 IDs, 6 matched),
   `--check` ok.
   `#discharges` does not list `chevalleyPerfect` as discharged: no proof of `ChevalleyPerfect` exists, the fold is a
   bypass; the field is gone from frozenTarget's hypotheses instead (closure check, OpenStatements).
