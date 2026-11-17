# fold33-pic (fleet note)

**Result.** phisurj's two removals, then piczero-char0's GLUE reduction, are folded into wip/leaf-fold33b
(base 943f1775). No existing declaration changed: the hash guard shows only additions plus `frozenTarget`.
wip/leaf-fold33b fast-forwards to wip/fold33-pic. Report: docs/research/fold33-pic.md; log: scratch/fold33-pic/log.md.

| | top | H (render_open) | open |
|---|---|---|---|
| base | sixContactMin_of_open43 | 31, strictest 11/20 | 37 |
| step 1 phisurj | sixContactMin_of_open45 | 29, 10/19 | 35 |
| step 2 piczero-char0 | sixContactMin_of_open46 | 31, 13/18 | 37 |

Step 1:
* `weilPairingMumford` was proved by autofold (TailZ51, `PhiSurj.weilPairingMumford_of_open`).
* `mumfordPhiSurjectiveAC` was rerouted without copies. TailZ52 enters the existing `sixContactMin_of_open37_hf_gm` at
  `OpenAddedLeaves18`, whose field `phiAmpleIsogeny` is now `PhiSurj.phiAmpleIsogeny_of_open`. The fold33-copy
  generators were therefore not needed.

Step 2: after step 1, every reader of `picZeroAbVar` is still in characteristic 0 (field taint on the folded tree).
* `Contrib/OneProof/PhiSurjCharZero.lean` (new) proves phisurj's theorems in characteristic 0 from `PicZeroAbVar0`. It
  compiled at the first attempt.
* `OneProof/H/PicZeroCharZeroCopy.lean` (generated, 96 blocks) and TailZ53 replace `picZeroAbVar` by `picLocFinType`,
  `identityComponentLFT` and `kleimanPicZeroProper`. These are published, flagged unread, locators UNVERIFIED.

**Compiles (VERIFIED).**
* `lake build +Main +Discharges` and the new modules (14223 jobs).
* `frozenTarget` rests on [propext, Classical.choice, Quot.sound].
* The closure contains none of `PicZeroAbVar`, `PicZeroSmooth`, `MumfordPhiSurjectiveAC`, `WeilPairingMumford` or
  `sorryAx`.
* OpenStatements, render_open --check, frontier_crosswalk --check, DischargesTest and the autoform check (OK, 781
  articles) all pass.

**Remains.**
* `MumfordPhiSurjectiveAC` and `PicZeroSmoothPosChar` are unproved, but neither is a hypothesis any more.
* The three new leaves need a reading against the printed sources.
* `mumfordTorsionAlgClosed` is proved on origin/proof/picard-fibres-20261116, which is not merged here.
