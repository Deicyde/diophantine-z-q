# mobius-glue results log

Base: 2dd83306 + merge origin/wip/qm-pin. Target: `LeafQM.AV.Pin.MobiusGlue`, copied verbatim
from `scratch/qm-pin/QMPin.lean` (lines 553-567).

## Build
- `lake build ZInQKernel.HDecomp.QM.Leaves`: success, 2m18s (build0.txt). VERIFIED.

## RatInj.lean (imports Mathlib only)
- `MobiusGlueDev.natDegree_le_one_of_injective`: K algebraically closed, char 0, F G coprime,
  `t ↦ [F(t) : G(t)]` injective on K → natDegree F ≤ 1 ∧ natDegree G ≤ 1 (Wronskian argument).
  run 3: 0 errors. VERIFIED (compiled).

## MobiusGlue.lean (imports ZInQKernel.HDecomp.QM.Leaves)
- §0: QMFamily, IsFibreOf, R1famProps, R1fpPropsPin, R1univProps, R1fpPropsU, MobiusGlue copied
  from scratch/qm-pin/QMPin.lean; text of each declaration identical (python string compare). VERIFIED.
- §1 Mob.ratEval, Mob.natDegree_le_one_of_injective (from RatInj.lean), Mob.ratEval_eq_self
  (deg ≤ 1, no finite pole, fixes 0 and c ≠ 0 ⇒ identity on K). compiled.
- §2 named facts (defs): CurveRatFactor, CurveSurj, TwistClassFinite.
- §3 mobiusGlue_of_curveFacts : CurveRatFactor → CurveSurj → TwistClassFinite → MobiusGlue. compiled.
- §4 AutOInnerFinite (def); exists_liftO_congr; level3_finite (TorsionStructure → Finite (Level3 q),
  char 0, via kernel Level3.torsor); transportLevel, QML3.isoTransport, conjUnitIso;
  twistClassFinite_of : TorsionStructure → AutOInnerFinite → TwistClassFinite. compiled.
- §5 mobiusGlue_of_named : CurveRatFactor → CurveSurj → ObjBridge.TorsionStructure →
  AutOInnerFinite → MobiusGlue. compiled.
- run (04:50): 0 errors, 0 warnings; 6 `#print axioms`, all [propext, Classical.choice, Quot.sound]. VERIFIED.
- §6 phi_part, SameTripleMor, transfer_pointwise_mor, sameTripleMor_of_mobius, pointwise_of_witness_mor
  copied from QMPin.lean (identical text, python compare, VERIFIED); new sameTripleMor_of_named,
  pointwise_of_witness_named (named facts in place of MobiusGlue). run (05:10): 0 errors; 8
  `#print axioms` all [propext, Classical.choice, Quot.sound]. VERIFIED.
- Hypotheses of MobiusGlue actually used by the proof: h1' (Y' proper, smooth rel. dim 1, has a
  ℚ̄-point), h2, h2', hCM, hg, and Φ' Qbar bijective. h1 (R1fpPropsU Y Φ), R1fam/R1univ of Y' unused.
