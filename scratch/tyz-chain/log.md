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
- 00:31 lake build ZInQKernel.Contrib.TYZChain.Main: OK first try (Lcal 26s, Lemma318 37s, Bridge 77s, Thm35 19s, L321 47s, Main 5s). VERIFIED.
- 00:32 lake build ZInQKernel.Contrib.TYZChain.ModFn ZInQKernel.Contrib.TYZChain.SSExponent: OK (49 s). VERIFIED.
- 00:33 `lake env lean scratch/tyz-chain/Check.lean` (6 s): 79 `#print axioms`, all
  `[propext, Classical.choice, Quot.sound]`; `#check` of the main theorem shows exactly the 5 hypotheses
  TYZThm11Integral, TYZLemma29Mod2, Shimura.ShimuraReciprocityModFn, T318.SqrtTwoNotInHHprime,
  ∀ ℓ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ. VERIFIED. Output in Check.out.
- 00:34 L321: replaced tyz-321's ~130-line copy of the absolute-Frobenius part of
  Contrib/Chebotarev/FrobeniusDenseOfExists.lean (VERIFIED identical up to GQ→GalQ and docstrings, by diff)
  by `import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists` + a selective `open`. Rebuild OK (L321 34 s,
  Main 4 s); Check.lean rerun: 79 × standard axioms. VERIFIED. (Consequence: Main now imports all of Mathlib
  transitively, through that module's `import Mathlib`.)
