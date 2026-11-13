"""Generate ImagePlaneFinal.lean: scratch/curve-glue/MobiusFinal.lean verbatim (without its
#print axioms lines), then this task's parts IC, AD, C2Kproof, then the final theorems.
Usage (repo root): python3 -I scratch/image-plane/mk_final.py"""
D = 'scratch/image-plane/'
rd = lambda p: open(p).read()
mf = rd('scratch/curve-glue/MobiusFinal.lean')
k = mf.index('\nend\n\n#print axioms') + len('\nend\n')
base = mf[:k]
assert base.rstrip().endswith('end')
parts = rd(D + 'IC.lean.part') + rd(D + 'AD.lean.part') + rd(D + 'C2Kproof.lean.part')
head = """
/-! # image-plane additions (task image-plane, 2026-11-13)

Everything above is `scratch/curve-glue/MobiusFinal.lean` verbatim (its `#print axioms` lines
dropped). Below: `scratch/image-plane/IC.lean.part` ((IC) `ImageClosed` from properness),
`AD.lean.part` ((AD) `AlgDep`) and `C2Kproof.lean.part` (C2K from (CI)), then the end-to-end
theorems: (G1') `ImagePlaneCurveClosed` with no hypothesis, and the kernel's `MobiusGlue` from
the textbook leaf T5 alone. -/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
open PkgI3
"""
final = """
/-- **C2K holds** (from (CI), proved by curve-glue). -/
theorem constOrOntoAlgClosed : ConstOrOntoAlgClosed :=
  constOrOntoAlgClosed_of_CI componentIrreducible

/-- **(AD) holds.** -/
theorem algDep : AlgDep :=
  algDep_of_CI smoothStalkDimOne componentIrreducible

/-- **(G1'') holds.** -/
theorem imagePlaneCurveIrr : ImagePlaneCurveIrr :=
  imagePlaneCurveIrr_of constOrOntoAlgClosed componentIrreducible algDep imageClosed

/-- **(G1') `ImagePlaneCurveClosed` holds** (task image-plane): no hypothesis, no leaf. -/
theorem imagePlaneCurveClosed : ImagePlaneCurveClosed :=
  imagePlaneCurveClosed_of componentIrreducible imagePlaneCurveIrr

/-- **(G1) holds.** -/
theorem imagePlaneCurve : ImagePlaneCurve :=
  imagePlaneCurve_of constOrOntoAlgClosed imagePlaneCurveClosed

/-- **C3K holds.** -/
theorem ratFactorAlgClosed : RatFactorAlgClosed :=
  ratFactorAlgClosed_of imagePlaneCurve

/-- **Both curve facts of mobius-glue hold.** -/
theorem curveFacts : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_leaves smoothStalkDimOne constOrOntoAlgClosed ratFactorAlgClosed

end Pin

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits Pin

/-- **The kernel's `MobiusGlue` from the textbook leaf T5 `ObjBridge.TorsionStructure` alone.** -/
theorem mobiusGlue_of_T5 (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_curves curveFacts.1 curveFacts.2 hT

/-- **Its CM-free form** (CM objects from the leaf bundle `R1R2fp`). -/
theorem mobiusGlueNoCM_of_T5 (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_T5 hT) h

end CurveGlue

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.imageClosed
#print axioms LeafQM.AV.Pin.constOrOntoAlgClosed
#print axioms LeafQM.AV.Pin.algDep
#print axioms LeafQM.AV.Pin.imagePlaneCurveIrr
#print axioms LeafQM.AV.Pin.imagePlaneCurveClosed
#print axioms LeafQM.AV.Pin.imagePlaneCurve
#print axioms LeafQM.AV.Pin.ratFactorAlgClosed
#print axioms LeafQM.AV.Pin.curveFacts
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_T5
"""
open(D + 'ImagePlaneFinal.lean', 'w').write(base + head + parts + final)
