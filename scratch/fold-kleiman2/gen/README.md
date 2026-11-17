# Replaying the fold-kleiman2 fold on a later head

The fold is a copy reroute (the new leaf `KleimanSection2.KleimanPicZeroProper954` is weaker than the field
`PicFix.KleimanPicZeroProper`, so `scripts/one_proof/autofold.py` cannot apply it). To replay it on a head that has
further autofolds:

1. Make sure `ZInQKernel/Contrib/OneProof/KleimanPicZero954.lean` (kleiman-section2, unchanged by this fold) is on
   the head (merge wip/kleiman-section2 or this branch's merge commit).
2. From the repository root: `python3 scratch/fold-kleiman2/gen/gen.py` (dry run: prints the module and, on stderr,
   the chain it copies), then `python3 scratch/fold-kleiman2/gen/gen.py --write`. It reads the top call
   `HDec.HSyn.sixContactMin_of_openM r t l` and the binder `(l : HDec.HSyn.OpenAddedLeavesA)` from
   `ZInQKernel/OneProof/Main.lean`, writes `ZInQKernel/OneProof/H/TailZ{K+1}.lean` (next free TailZ number, next free
   `OpenAddedLeaves` and `sixContactMin_of_open` numbers) and patches Main (import, binder, top call).
   It stops with an error if the added bundle no longer has `kleimanPicZeroProper` or `picRepresentableAbVar`, if a
   new reader of `l.kleimanPicZeroProper` appears (extend `REPLACE`), or if the chain changes the added bundle type
   above `openAddedLeaves24_of_OpenAddedLeaves25` (a later autofold of an added field: then fold this first, or extend
   the walk to copy that conversion).
3. Update the docstring paragraph of Main.lean if wanted; kinds.tsv: drop the row `added kleimanPicZeroProper`, add
   `scratch/fold-kleiman2/kinds-row.tsv`; claims.tsv: drop the row `kleimanPicZeroProper`.
4. Build and checks as in `scratch/fold-kleiman2/log.md`.
