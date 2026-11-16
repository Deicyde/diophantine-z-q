# scratch/pic-smooth

Report: docs/research/pic-smooth.md. Lean: ZInQKernel/Contrib/OneProof/PicZeroSmoothCartier.lean (Cartier as a
hypothesis) and PicZeroAbVarCartier.lean (Cartier from cartierSmooth_proof, merged from origin/cloud-b3/w16-h98).

* log.md: results log.
* Discharges.lean / discharges.txt: #discharges output (56 open, 3085 checked, 21 discharge one).
* Axioms.lean / axioms.txt: standard axioms for picZeroAbVarAt_charZero, picZeroSmooth_of_cartier,
  picZeroAbVar_of_printed2.
* autofold.json (recommended once CartierSmooth.lean is on main): picZeroAbVar, 34/11 -> 37/11.
* autofold-both.json: with pic-fix's phiAmpleIsogeny, 34/11 -> 39/10.
* autofold-cartierleaf.json: for a main without CartierSmooth.lean, 34/11 -> 38/11.
* FoldDryRun*.lean: the dry-run modules (line 1 stripped); each compiles to sixContactMin_of_open36.
* build-*.txt: build logs.
