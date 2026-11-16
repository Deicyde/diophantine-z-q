# scratch/pic-fix2

Report: docs/research/pic-fix2.md. Log: log.md.

* Reading.lean: the scratch version of ZInQKernel/Contrib/OneProof/PhiAmpleIsogenyReading.lean, with `#print axioms`.
* Discharges.lean, discharges.txt: `#discharges` against Main.
* autofold.json: fold A, `phiAmpleIsogeny` with 3 leaves (34/11 -> 37/10, strict and strictest). FoldDryRun.lean
  compiles.
* narrow.patch + autofold-narrow.json: fold B, the field narrowed to `phiVeryAmpleIsogeny`, 2 leaves
  (34/11 -> 36/10, strict and strictest). Tested on a throwaway copy; NarrowFold-TailZ43.lean.txt is the module it
  generated.
* autofold-both.json: fold A plus pic-fix's picZeroAbVar (-> 40/10). FoldDryRunBoth.lean compiles.
* autofold-picfix-strictest.json: pic-fix's spec with its KL leaf flagged "strictest reading" (strictest 0).
