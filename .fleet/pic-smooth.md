# pic-smooth (fleet note)

**Verdict.** The target "picZeroAbVar from LEAF leaves only, −1, PicZeroSmooth gone" is not reachable as stated:
`PicDict.PicZeroSmooth` and the field `picZeroAbVar` quantify over every field, and Cartier's theorem
(`AVGlue.CartierSmooth`, `[CharZero k]`) covers characteristic 0 only. In characteristic p, Pic⁰ of an abelian
variety is smooth by Mumford §13, which is not a consequence of Cartier (μ_p, Igusa's surface).

**Proved (compiled, standard axioms):**
* `PicSmooth.picZeroSmooth_of_cartier : CartierSmooth → PicLocFinType → PicZeroSmoothPosChar → PicZeroSmooth`
  (char 0: P is a group scheme lft by `picardFunctorCommGrpObj` + PicLocFinType, smooth by Cartier, opens of
  smooth are smooth).
* `PicSmooth.picZeroAbVar_of_printed2 : PicLocFinType → IdentityComponentLFT → PicZeroSmoothPosChar →
  KleimanPicZeroProper → PicZeroAbVar` (Cartier by `cartierSmooth_proof`).
* `PicSmooth.picZeroAbVarAt_charZero`: PicZeroAbVar at every char-0 field from the three LEAF statements alone.
* Files: ZInQKernel/Contrib/OneProof/PicZeroSmoothCartier.lean (no h98 import), PicZeroAbVarCartier.lean.
  Merged origin/cloud-b3/w16-h98 (68 added files, CartierSmooth.lean), the only branch with cartierSmooth_proof.
* #discharges: picZeroAbVar discharged, still assuming the 3 leaves + PicZeroSmoothPosChar.
* Autofold dry runs (compile): picZeroAbVar alone 34/11 -> 37/11 (0); with pic-fix's phiAmpleIsogeny 34/11 ->
  39/10 (−1); fallback without CartierSmooth.lean on main 34/11 -> 38/11.

**Remains.** `PicZeroSmoothPosChar` (GLUE, pending reading: one print over an arbitrary field, BLR 8.4 / FGA
Explained 9.5 / Milne 1986 §10). Or a consumer restriction to char 0 (picZeroAbVar → t09SymmIsogenyExists →
DetTate (number fields) and T9 → G12Det (number fields)); then picZeroAbVarAt_charZero gives −1 from LEAF leaves
only. CartierSmooth.lean must land on main before autofold.json folds.
