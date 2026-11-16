# leaf-fold33 results log

Base: 6b7a45445 (lf32b: 37 H fields, strict 16 LEAF / 21 GLUE, top sixContactMin_of_open38 in TailZ45).

## Decisions before merging

* pic-fix2 (45945e9ce): fold B is `scratch/pic-fix2/narrow.patch` + `autofold-narrow.json` (README, report §1, §3).
  The patch edits the existing modules TailZ24, 26, 30, 31, 34 (field `phiAmpleIsogeny` renamed and retyped
  `phiVeryAmpleIsogeny`, and `addedLeaves12_of_open13` rewritten). In lf32b `phiAmpleIsogeny` is no longer a field:
  TailZ45 fills it by `PicFix.phiAmpleIsogeny_of_printed n.mumfordKLFiniteSectionAC n.mumfordPhiSurjectiveAC`.
  Fold B's leaves (`MumfordKLFiniteDivisorAC`, `MumfordPhiSurjectiveVAC`) assume `IsVeryAmple` in addition to
  `IsAmple`, so they are weaker than the open leaves `PicFix.MumfordKLFiniteSectionAC` (ample + nonzero section)
  and `PicDict.MumfordPhiSurjectiveAC` (ample) and cannot discharge them. Fold B therefore needs hand edits of
  existing H modules, which this task may not make. Decision: skip, do not merge.

## Merges

* poincare-proof 5795bbc01: merged, no conflict. The merge brought an older generated STATUS.md; restored to the
  lf32b version (regenerated at the end).
* neron-sh-proof 3842078af: merged, no conflict.
* pic-smooth 2128db760: merged, no conflict. Its 68 CloudB3W16Cartier files and CartierSmooth.lean (from the h98
  branch) were already in lf32b, byte-identical, so the merge adds only PicZeroSmoothCartier.lean,
  PicZeroAbVarCartier.lean, the report and scratch files.
* pic-fix2 45945e9ce: not merged (see above).

## Adaptations

* neron-sh-proof: `DictModels.NeronBLR72.BLR_7_2_1` is `def BLR_7_2_1 : Prop := ReductGlue.NeronBaseChangeUnramifiedDVR`
  (NeronBaseChangeBLR72.lean:43), and the contribution proves `NeronSH.neronBaseChangeUnramifiedDVR_proof :
  ReductGlue.NeronBaseChangeUnramifiedDVR`. Adapter `ZInQ.Contrib.OneProof.Fold33.blr_7_2_1_proof` in
  ZInQKernel/Contrib/OneProof/Fold33/NeronBLR.lean (term-mode, by unfolding). Spec discharges `blr_7_2_1`, no leaves.
  The original discharge of `neronBaseChangeStrictHenselization` is dropped (no longer a field).
* poincare-proof: `{l}.phiAmpleIsogeny` -> `_root_.PicFix.phiAmpleIsogeny_of_printed {l}.mumfordKLFiniteSectionAC
  {l}.mumfordPhiSurjectiveAC` (TailZ45:123); `{l}.milneIsogenyQuasiInverse` ->
  `_root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof`; `{n}.cartierSmooth` ->
  `_root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof` (TailZ44:118); `{l}.picZeroAbVar` -> the
  pic-smooth term (picZeroAbVar is discharged in the same fold, so the new added bundle has no such field).
* pic-smooth: README recommends autofold.json once CartierSmooth.lean is on the base; it is, so autofold.json is
  used unchanged (picZeroAbVar by PicSmooth.picZeroAbVar_of_printed2, leaves picLocFinType, identityComponentLFT,
  picZeroSmoothPosChar, kleimanPicZeroProper; kinds and flags kept).

## Checks

* Forbidden-token scan (sorry, axiom, native_decide, run_cmd, #eval, initialize, extern, implemented_by, admit) of
  PoincareComplement.lean, NeronBaseChangeStrictHenselization.lean, PicZeroSmoothCartier.lean,
  PicZeroAbVarCartier.lean, Fold33/NeronBLR.lean: no hits. No vendored file changed by the merges.
* Combined spec scratch/leaf-fold33/autofold.json, --dry-run: `strict count: 16/21 on 37 -> 18/20 on 38;
  strictest 16/21 -> 18/20` (output scratch/leaf-fold33/autofold-dryrun.txt).

## Rerun (continued after the dry run)

* The earlier contribution build log was cut off at [12880/12886] with no errors (run interrupted); the build of
  PoincareComplement, NeronBaseChangeStrictHenselization, Fold33.NeronBLR, PicZeroSmoothCartier and
  PicZeroAbVarCartier is being rerun.
* Step (a), main: `git merge-base --is-ancestor 5e235a40 origin/main` fails (origin/main = e41a71697), so 5e235a40
  (origin/wip/integrate-w82) was merged: commit 075e3622c. Its only change against lf32b is STATUS.md (main's
  NVLocalInertia wording). Conflict resolved by keeping the branch's STATUS.md: the paragraph main reworded is no
  longer in the branch's STATUS.md (lf32b rewrote that section when NVLocalInertia left the chain), so main's hunk has
  nothing to apply to. (The merge commit message says "plus main's NVLocalInertia wording"; in fact no hunk applied.)
* Step (b), supplier PRs (first check): origin/pr/23 0eab413df, pr/25 7c9177bd9, pr/29 fefce8ef0, pr/31 d42bb38f4,
  pr/34 4fa17fc59, pr/35 37a970528, pr/36 47ca4df21, pr/38 a9bc2e35c are all ancestors of HEAD; nothing to merge.
  Rechecked before the final check.
* Contribution build (rerun): `lake build` of PoincareComplement, NeronBaseChangeStrictHenselization, Fold33.NeronBLR,
  PicZeroSmoothCartier, PicZeroAbVarCartier: RC=0, "Build completed successfully (12886 jobs)", no errors, no
  "environment already contains".
* Axioms (scratch/leaf-fold33/Axioms.lean): poincareComplement_of_open, Fold33.blr_7_2_1_proof,
  NeronSH.neronBaseChangeUnramifiedDVR_proof, PicSmooth.picZeroAbVar_of_printed2, CartierSmooth.cartierSmooth_proof:
  each [propext, Classical.choice, Quot.sound]. (PicFix.phiAmpleIsogeny_of_printed and milneIsogenyQuasiInverse_proof
  are lf32b terms not imported by these modules; they are already in Main through TailZ44/45 and are checked by the
  final frozenTarget axioms line.)
* Final check, first run (on 744902a12): BUILD-RC=1. TailZ46.lean:105 "Invalid field notation ... l has type
  OpenAddedLeaves20": autofold writes the textbook conversion (poincareComplement, whose proof reads {l}) before the
  new structure OpenAddedLeaves20 of the same module, so the name is an auto-bound implicit there. One spec cannot both
  discharge a field from {l} and replace the added bundle. The later steps ran on stale oleans (CHECK-RC=1, kinds rows
  mismatched); no generated docs were committed.
* Fix: the autofold commit reverted (git revert 744902a12) and the fold split into two autofolds with the same
  discharges: scratch/leaf-fold33/autofold-a.json (poincareComplement with {l}.picZeroAbVar, the field still present in
  OpenAddedLeaves19, and blr_7_2_1) and autofold-b.json (picZeroAbVar by pic-smooth). The combined autofold.json is
  kept for the record. Fold a: `16/21 on 37 -> 15/20 on 35` (TailZ46, sixContactMin_of_open39); fold b:
  `15/20 on 35 -> 18/20 on 38` (TailZ47, sixContactMin_of_open40), the same end state as the combined spec.
