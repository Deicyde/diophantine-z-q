
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

/-- **FS5 with the repaired clauses, from leaves and named glue only, with mobius-glue's curve
facts**: the bundle, R5fpCount, T5, T6, T27, N1b (leaves), and `CurveRatFactor`, `CurveSurj`,
N2 (glue). -/
theorem fibreComTrivialFull_of_curves_leaves (hL : R1R2fpFull) (hRF : CurveRatFactor)
    (hSu : CurveSurj) (hT : ObjBridge.TorsionStructure) (t27 : PkgI3.QMDichotomyYu)
    (t6 : PkgI3.HomFreeFinite) (hB : CMConductorCoprime6) (hK : X6KummerFibre)
    (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of_leaves' hL (mobiusGlue_of_curves hRF hSu hT) t27 t6 hB hK hC

/-- **The same with N1b reduced to Shimura's description of CM points** (`CMOptimalEmbedding`):
leaves the bundle, R5fpCount, T5, T6, T27, `CMOptimalEmbedding`; glue `CurveRatFactor`,
`CurveSurj`, N2. -/
theorem fibreComTrivialFull_of_curves_leaves' (hL : R1R2fpFull) (hRF : CurveRatFactor)
    (hSu : CurveSurj) (hT : ObjBridge.TorsionStructure) (t27 : PkgI3.QMDichotomyYu)
    (t6 : PkgI3.HomFreeFinite) (hE : CMOptimalEmbedding) (hK : X6KummerFibre)
    (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of_leaves'' hL (mobiusGlue_of_curves hRF hSu hT) t27 t6 hE hK hC

end FS5NoCM

#print axioms FS5NoCM.fibreComTrivialFull_of_curves
#print axioms FS5NoCM.fibreComTrivialFull_of_curves_leaves
#print axioms FS5NoCM.fibreComTrivialFull_of_curves_leaves'
