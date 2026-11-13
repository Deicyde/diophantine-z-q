# fibre-qm-period results log

Base: 2dd83306 + merges of origin/wip/qm-pin, origin/wip/mobius-glue (g0-thetapoint already in base).

## Files
- `build.sh`: assembles `FQMBase.lean` = g0-thetapoint's `ThetaPoint.lean` with qm-pin's full edit
  (`apply_edit.py ... full`: `R1famProps`, `R1univProps` appended to `R1fpProps`; 2 obtain patterns)
  + `part_pin.lean` (qm-pin's `Pin` lemmas copied verbatim from `QMPinKernelFull.lean`: `phi_part`,
  `SameTripleMor`, `transfer_pointwise_mor`, `MobiusGlue`, `sameTripleMor_of_mobius`,
  `pointwise_of_witness_mor`, `cm_objects_of_R1R2fp`, plus `R1fpProps.univ`);
  `FibreQM.lean` = `FQMBase.lean` + `part_fqm.lean` (this task).
- Dev loop: `lake env lean -o olean/FQMBase.olean FQMBase.lean` once, then `Dev.lean` = `import FQMBase` +
  `part_fqm.lean` with `LEAN_PATH=$(lake env printenv LEAN_PATH):scratch/fibre-qm-period/olean`.

## Compile outcomes
- prereq: `lake build ZInQKernel.HDecomp.Analytic.QMLattice ZInQKernel.Hypotheses.JHeight` OK (2m0s).
- run_base (05:30): `FQMBase.lean` (20634 lines) 0 errors, 2m52s. VERIFIED.
- run_dev1: errors (`γ` is a token in this context; `*ᵥ` needs `open Matrix`). Fixed.
- run_dev2 (05:37): `Dev.lean` 0 errors, 4.8s; 9 `#print axioms` all `[propext, Classical.choice, Quot.sound]`. VERIFIED.
