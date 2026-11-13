# mobius-glue results log

Base: 2dd83306 + merge origin/wip/qm-pin. Target: `LeafQM.AV.Pin.MobiusGlue`, copied verbatim
from `scratch/qm-pin/QMPin.lean` (lines 553-567).

## Build
- `lake build ZInQKernel.HDecomp.QM.Leaves`: success, 2m18s (build0.txt). VERIFIED.

## RatInj.lean (imports Mathlib only)
- `MobiusGlueDev.natDegree_le_one_of_injective`: K algebraically closed, char 0, F G coprime,
  `t ↦ [F(t) : G(t)]` injective on K → natDegree F ≤ 1 ∧ natDegree G ≤ 1 (Wronskian argument).
  run 3: 0 errors. VERIFIED (compiled).
