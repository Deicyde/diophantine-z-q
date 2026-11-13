# period-glue results log

Task period-glue, 2026-11-13. Base 6f296292 + merge of origin/wip/period-map (already contained).
Targets: period-map's glue `S8Nonzero`, `S8WeightExact`, `SphereFactorAffine`,
`BaseChangeClassUnique`, `PiTwistC`, `QMTwistLattice`; restate leaves `ValenceBoundGammaStar`,
`CMDescends`.

## Setup
- `build_base.sh`: `PGBase.lean` = fibre-qm-period FibreQM.lean lines 1-20634 + part_fqm.lean +
  period-map part_light/theta/siegel/order/heavy (verbatim; = period-map's DevHeavy without the
  import). `run_base1.txt`: 0 errors, 3m13s. VERIFIED.
- prereq `lake build ...QMLattice ...JHeight ...HeightConstant ...Objects`: OK 1m25s (`run_prereq.txt`).

## BaseChangeClassUnique — PROVED (VERIFIED, run_bcu.txt)
- `BCU.lean`: `PeriodGlue.baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique`.
  Axioms `[propext, Classical.choice, Quot.sound]`.
- Inputs: Mathlib only; rigidity `isMonHom_of_geometricallyIntegral` copied verbatim from
  scratch/mul-rigidity/Rigidity.lean (namespace renamed `PeriodGlue.MulRigidity`).
- Proof: comparison map from the pullback property; every compatibility checked after composing
  with `g'` (`eq_of_comp`); level clause at `a = 0` gives identity → identity; rigidity.
