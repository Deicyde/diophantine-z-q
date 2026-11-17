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
