
/-! ## §F FS5 from the curve facts of mobius-glue -/

namespace FS5NoCM

open LeafQM.AV LeafQM.AV.Pin ZInQ ZInQ.JHeight

/-- **FS5 with the repaired QM clauses, from named Props only**: the leaf bundle (after qm-pin's
full edit), the leaf R5fpCount, the textbook leaf T5 (`ObjBridge.TorsionStructure`), the curve
glue `CurveRatFactor`, `CurveSurj` (mobius-glue), and NoCM's inputs N1a, N1b, N2. -/
theorem fibreComTrivialFull_of_curves (hL : R1R2fpFull) (hRF : CurveRatFactor)
    (hSu : CurveSurj) (hT : ObjBridge.TorsionStructure) (hA : ComIntOrQuadOrder)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL (mobiusGlue_of_curves hRF hSu hT) hA hB hK hC

end FS5NoCM

#print axioms FS5NoCM.fibreComTrivialFull_of_curves
