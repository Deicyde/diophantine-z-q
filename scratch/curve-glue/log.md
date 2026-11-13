# curve-glue results log

## 1. CM points for MobiusGlue (`CMPoints.lean`)
- Compiled 06:3x, 0 errors 0 warnings; axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
- `cm_points_of_objects : R2fpProps Y Φ π → CMObjects → CMPoints Y Φ π` (Φ onto; one-way clauses suffice).
- `cm_points_of_R1R2fp`, `cm_points_of_R1R2fpRep` (CMExists from R2X6PropsIff + X6Surj.1; level-3 from X6Surj.2).
- `mobiusGlue_noCM_of(_rep) : MobiusGlue → bundle → MobiusGlueNoCM`.
- Finding: kernel `MobiusGlue` already has the CM objects as a premise; consumers already supply them
  (`cm_objects_of_R1R2fp`, pin-apply `sameTripleMor_of_leaves`). Gap is closed; no statement changes.
