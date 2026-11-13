# ts-kummer results log

Task: prove or reduce the seven Kummer pieces of scratch/prop-ts-glue/PropTSGlue.lean
(KummerCompositum; KummerAbhyankarFinGlue, KummerOtherBranchFin, KummerVerticalFin;
KummerAbhyankarInfGlue, KummerOtherBranchInf, KummerVerticalInf), the open glue under
`PropTSRed.KummerMeetGlue` via `PropTSGlue.kummerMeetGlue_of_pieces'`.

## Step 0: setup
- Merged origin/wip/prop-ts-glue (clean).
- Truth check of the seven statements (re-derived, model argument, no Lean): all seven true as
  stated (agrees with prop-ts-glue's review). Key point for the Abhyankar pieces: Mathlib's
  `Ideal.ramificationIdx` is the length of `S_q / p S_q`, intrinsic to the local ring, so
  `ramificationIdx_map_eq_ramificationIdx` (localization of the base) and `ramificationIdx_tower`
  (flat towers) apply.
- Plan: (1) prove KummerAbhyankarFinGlue and KummerAbhyankarInfGlue from T2 through one abstract
  core lemma; (2) reduce the other-branch and vertical pieces to a compositum-unramified Prop;
  (3) KummerCompositum.
