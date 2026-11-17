# piczero-char0 (fleet note)

**Result: strict GLUE −1, no new GLUE.** On leaf-fold33b 0e3c3125, `picZeroAbVar` (T09Pic.PicZeroAbVar, GLUE) is used in
frozenTarget's closure only in characteristic 0 or not at all (field-level taint, VERIFIED): via t09SymmIsogenyExists
→ detTate_of_leaves4 (number fields) and → t9 (dead: only the discarded antecedent of G12Det), via
mumfordKLFiniteSectionAC/phiAmpleIsogeny (feeding only those), and via poincareComplement (statement already char 0).

**Compiles (standard axioms):**
- `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZero.lean`: `PicZeroChar0.picZeroAbVar0_of_leaves : PicLocFinType →
  IdentityComponentLFT → KleimanPicZeroProper → PicZeroAbVar0` (Cartier via cartierSmooth_proof; no PicZeroSmoothPosChar),
  plus char-0 versions of the four reader proofs.
- `ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZeroReroute.lean` (generated, 101 copied decls, 9 s):
  `sixContactMin_of_open41_pz` from OpenAddedLeaves20PZ (picZeroAbVar weakened to char 0). Closure check: no
  T09Pic.PicZeroAbVar, T09_SymmIsogenyExists, T09_WeilPairing, PicZeroSmooth, sorryAx.
- scratch/piczero-char0/FoldCheck.lean: OpenAddedLeaves21 (OAL20 − picZeroAbVar + picLocFinType, identityComponentLFT,
  kleimanPicZeroProper, all LEAF flagged unread as rated by pic-fix/pic-smooth), `frozenTarget_pz`.

**Counts:** 33 fields strict 13/20, strictest 13/20 → 35 fields strict 16/19, strictest 16/19.

**Remains:** integration (manual fold, scratch/piczero-char0/fold-spec.md; autofold cannot express a reroute;
regenerate with Taint2.lean + gen.py if carriers move). #discharges cannot show a reroute (18 projection-noise lines).
PicZeroSmoothPosChar (Mumford §13, char p) is unproved and no longer needed. Locators of the three leaves UNVERIFIED.

Last update: 11-16 18:10 PST; all checks above re-run on this branch.
