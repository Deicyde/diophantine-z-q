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
