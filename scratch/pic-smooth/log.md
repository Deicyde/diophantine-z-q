# pic-smooth results log

Base: wip/pic-fix be79cb5b. `git merge origin/main`: already up to date (main = 2880fef1e is in the base).

## Cartier's theorem in the tree
* VERIFIED (git): `cartierSmooth_proof : AVGlue.CartierSmooth` (ZInQKernel/Contrib/OneProof/CartierSmooth.lean) exists
  only on `origin/cloud-b3/w16-h98` (4fa17fc59, 68 added files, no modified file), not on origin/main.
  Merged into wip/pic-smooth (additive merge, no conflict).
* VERIFIED (read): `AVGlue.CartierSmooth` (ZInQKernel/OneProof/H/TailP.lean:305):
  `∀ (k : Type) [Field k] [CharZero k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], LocallyOfFiniteType G.hom → Smooth G.hom`.
  Hypotheses available for the Picard scheme P: `GrpObj P` from `picardFunctorCommGrpObj A.X.hom rep` (CommGrpObj),
  `LocallyOfFiniteType P.hom` from `PicLocFinType`. `CharZero K` is NOT available: `PicDict.PicZeroSmooth`
  and the bundle field `picZeroAbVar : T09Pic.PicZeroAbVar` quantify over every field.

## Finding
* VERIFIED (read): `PicDict.PicZeroSmooth` is `∀ (K : Type) [Field K] (A : AbVar K) ...`, all characteristics.
  Cartier gives the characteristic-0 case only. In characteristic p the claim is true (Mumford §13, STANDARD,
  locator UNVERIFIED) but not a consequence of Cartier. So PicZeroSmooth cannot be removed by Cartier alone.
* Consumers: picZeroAbVar is read only by `T09Pic.t09SymmIsogenyExists_of_four` (TailZ24.lean:807), whose target
  `WeilPairing.T09_SymmIsogenyExists` is again ∀ fields (TailB.lean:3752), consumed by detTate_of_leaves4 (TailK)
  and t9_of_leaves5 (TailN). A char-0 restriction would need a consumer-restricted refactor of pinned modules.

## Lean (all VERIFIED: compiled, `#print axioms`/#discharges give [propext, Classical.choice, Quot.sound])
* `lake build ZInQKernel.Contrib.OneProof.CartierSmooth` (merged h98 files): success, 9164 jobs, 2 min.
* New file ZInQKernel/Contrib/OneProof/PicZeroAbVarCartier.lean (namespace PicSmooth), imports
  Contrib.OneProof.PicZeroAbVar and Contrib.OneProof.CartierSmooth. `lake build` success (12879 jobs), first try.
  - `picard_smooth_of_cartier`: CartierSmooth → PicLocFinType → [CharZero K] → Smooth P.hom.
  - `picZeroSmoothAt_charZero`: PicZeroSmooth at each char-0 field (open subscheme of smooth P; the
    identity-component hypothesis is not used).
  - `picZeroAbVarAt_of`: pic-dict's proof of picZeroAbVar_of_leaves with K fixed.
  - `picZeroAbVarAt_charZero`: PicZeroAbVar at every char-0 field from PicLocFinType, IdentityComponentLFT,
    KleimanPicZeroProper only (Cartier by cartierSmooth_proof).
  - new Prop `PicZeroSmoothPosChar` (PicZeroSmooth restricted to CharP K p, p prime) — GLUE, pending reading.
  - `picZeroSmooth_of_cartier : CartierSmooth → PicLocFinType → PicZeroSmoothPosChar → PicZeroSmooth`.
  - `picZeroAbVar_of_printed2 : PicLocFinType → IdentityComponentLFT → PicZeroSmoothPosChar → KleimanPicZeroProper → PicZeroAbVar`.
* #discharges (scratch/pic-smooth/discharges.txt): `56 open hypotheses, 3085 theorems checked, 21 discharge one`;
  picZeroAbVar by PicSmooth.picZeroAbVar_of_printed2 still assumes
  [PicLocFinType, IdentityComponentLFT, PicZeroSmoothPosChar, KleimanPicZeroProper]; also
  OpenTextbookLeaves12.cartierSmooth by cartierSmooth_proof (from the merged branch).
* autofold dry runs (this base, re-rated): autofold.json (picZeroAbVar alone): `34/11 on 45 -> 37/11 on 48`
  (0); autofold-both.json (with pic-fix's phiAmpleIsogeny): `34/11 on 45 -> 39/10 on 49` (−1, same as pic-fix's
  autofold-both). Both dry-run modules compile to sixContactMin_of_open36 with the standard axioms.
* Net: PicZeroSmooth (all fields, GLUE) replaced by PicZeroSmoothPosChar (char p only, GLUE pending reading):
  the GLUE count does not drop; the target −1 for picZeroAbVar is not reached because the field is ∀ K.

## Split (so the reduction builds without the h98 files)
* ZInQKernel/Contrib/OneProof/PicZeroSmoothCartier.lean: everything with `hC : AVGlue.CartierSmooth` as a
  hypothesis; imports only Contrib.OneProof.PicZeroAbVar (AVGlue.CartierSmooth comes from TailP via the chain).
* ZInQKernel/Contrib/OneProof/PicZeroAbVarCartier.lean: imports it and CartierSmooth.lean; `picZeroAbVar_of_printed2`,
  `picZeroAbVarAt_charZero`. Both build (12880 jobs). Axioms.lean: standard axioms for all three main theorems.
* autofold-cartierleaf.json (for a main without CartierSmooth.lean: Cartier repeated as an added-bundle leaf
  `cartierSmoothPic`, flagged unread): `34/11 on 45 -> 38/11 on 49`; dry run compiles (standard axioms).
* #discharges rerun with both files: same lines, `56 open hypotheses, 3085 theorems checked, 21 discharge one`.
