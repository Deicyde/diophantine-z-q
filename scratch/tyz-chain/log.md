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
- 00:38 SSExponent: its §1–§3 (scratch lines 35–310) were a verbatim copy of tyz-318's §S (T318SS; VERIFIED by
  diff, identical except the position of `Ek`); now imported from TYZChain.Lemma318 with `open T318SS`.
  Added `t318_supersingularExponentA : T318.SupersingularExponentA` and
  `lemma318Literal_HHprime_of_sqrtTwoNotIn_ss`. Build OK (6.5 s); Check rerun: 81 × standard axioms. VERIFIED.
- 00:45 Bridge §14: replaced cm-bridge's verbatim copies of tyz-cm's declarations (namespace TyzCm: kappa,
  idealMeetOrder, idealLat, discOf, ShimuraReciprocityPic; helpers sqrt_mul_self_C, kappaRoot, kappaAlg,
  kappaAlg_apply, kappaZ, kappaLin, kappaLin_apply — the helpers VERIFIED identical by diff with
  TYZGenus/ShimuraZn.lean lines 41–66; the TyzCm Prop was rfl-checked by cm-bridge) by a selective
  `open ZInQ.Contrib.TYZGenus.Shimura (...)`. Rebuild of Bridge/Thm35/L321/Main OK (1m48); Check rerun OK. VERIFIED.
- 00:52 ModFn: shimura-modfn's §0 verbatim copies of Shimura.IsRatModFn / Shimura.ShimuraReciprocityModFn replaced
  by a selective open of the originals (rfl checks kept, now trivial). Build OK (131 s); Check rerun: 81 × standard. VERIFIED.
- 01:05 New module TYZChain/Headline.lean: `TYZChainLeaves` (structure of the five hypotheses),
  `tyzThm35ReadingA_of_tyzChainLeaves`, `frozenTarget_of_sixContactMin_grossZagier_tyzChainLeaves :
  SixContactMin → GrossZagier → TYZChainLeaves → FrozenTarget` (headline with the two proved providers
  heckeContinuation, functionalEquation5). Build OK (6.7 s); Check rerun: 83 × standard axioms. VERIFIED.
- 01:20 sqrt2-glue reported (84107b66): SqrtTwoNotInHHprime PROVED. Merged origin/wip/sqrt2-glue (clean).
- 01:25 New module TYZChain/Sqrt2Glue.lean = scratch/sqrt2-glue/Sqrt2Glue.lean with its §0 copies of tyz-318
  (SqrtTwoNotInHHprime, SigmaLift, Hprimebar_eq, sigma_moves_sqrtTwo, sqrtTwoNotInHHprime_of_sigmaLift; each
  VERIFIED byte-identical to TYZChain/Lemma318.lean) replaced by import + selective open of T318. Build OK (24 s).
- 01:28 Main: hypothesis h2 dropped (discharged by Sqrt2Glue.sqrtTwoNotInHHprime); new
  `package_lemma318Literal_HHprime` (TYZ Lemma 3.18, no hypotheses). Headline: field sqrtTwoNotIn dropped.
  Build OK; Check rerun: 89 × standard axioms; #check shows 4 hypotheses (all LEAF). VERIFIED.
