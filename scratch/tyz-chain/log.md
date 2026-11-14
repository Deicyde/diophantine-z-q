# tyz-chain results log

## 2026-11-14 00:21 start
- Fresh run (no earlier log). Base 67c2daf9.
- Merged origin/wip/tyz-318 (94b05c87), origin/wip/shimura-modfn (6bc73469), origin/wip/tyz-321 (c5908c68),
  origin/wip/ss-exponent (8b343fa8): all clean merges.
- origin/wip/sqrt2-glue: only a merge of tyz-318 so far (no report) -> not merged yet; recheck later.
- Build cache: copied (reflink) the oleans of a w49 checkout; only ShimuraMain (docstring) and
  SmoothFibre differ in the source trees, lake rebuilds those.
- Plan (structure of the scratch files, VERIFIED by diff):
  * cm-bridge Bridge.lean lines 1-3213 = namespace CMBridge (§0-§15).
  * tyz-321 L321.lean lines 1-3213 are identical to Bridge.lean 1-3213; 3214-5477 are new (T321B, T321).
  * tyz-35 Final.lean = Bridge 1-3212 with namespace renamed TYZ35, plus new §T, §G (lines 3204-3914).
  * tyz-318 Lemma318.lean, tyz-lcal TYZLcal.lean, shimura-modfn ModFn.lean, ss-exponent SSExponent.lean:
    standalone files on built modules.
