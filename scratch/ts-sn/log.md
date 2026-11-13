# ts-sn results log

## Step 0: setup (2026-11-13 09:16 PST)
- Base: origin/wip/prop-ts-glue merged (0ac06bd1). `scratch/ts-sn/TSSN.lean` starts as a verbatim
  copy of `scratch/prop-ts-glue/PropTSGlue.lean` (both target Props and their dependencies verbatim).
- Finding: `VerticalResidueSeparable` is already a theorem in that file:
  `verticalResidueSeparable_of_degree verticalResidueDegree` (prop-ts-glue step 13). Remaining
  target: `SNSpecialize`.
