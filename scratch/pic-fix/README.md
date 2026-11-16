# scratch/pic-fix

* `KLSection.lean`: (1) `MumfordKLFiniteSectionAC` (printed form) and the ample case; `phiAmpleIsogeny_of_printed`.
* `PicZeroProperN.lean`: (2) `KleimanPicZeroProper` over geometrically normal X, AbVar case; `picZeroAbVar_of_printed`.
* `Discharges.lean` / `discharges.txt`: `#discharges` run and output.
* `autofold.json` (phiAmpleIsogeny alone, recommended), `autofold-both.json` (+ picZeroAbVar);
  `FoldDryRun.lean`, `FoldDryRunBoth.lean`: their dry-run modules (line 1 stripped; compile to sixContactMin_of_open36).
* `log.md`: results log.

The deliverable Lean files are `ZInQKernel/Contrib/OneProof/PhiAmpleIsogeny.lean` and `PicZeroAbVar.lean`
(the two scratch files without `#print axioms`). Report: `docs/research/pic-fix.md`.
