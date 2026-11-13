"""Generate CurveGlueAll.lean, MobiusEnd.lean and MobiusFinal.lean from their parts.
Usage (repo root): python3 -I scratch/curve-glue/py/assemble.py"""
D = 'scratch/curve-glue/'
rd = lambda p: open(p).read()
ENDMARK = "end Pin\n\nend AV\n\nend LeafQM\n\nend\n"

# ---------- CurveGlueAll ----------
cf = rd('scratch/curve-facts/CurveFacts.lean'); c2 = rd(D + 'C2K.lean'); c3 = rd(D + 'C3K.lean')
cf_head = cf[:cf.index(ENDMARK)]
c2_body = c2[c2.index("/-! ## §1 Values of sections"):c2.index(ENDMARK)]
c3_body = c3[c3.index("/-! ## §1 Algebra"):c3.index(ENDMARK)]
cf_imports = "import ZInQKernel.HDecomp.QM.Pairs\nimport Mathlib.LinearAlgebra.Lagrange\n"
assert cf_head.startswith(cf_imports)
imports = cf_imports + """import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
"""
note = """
/-! # curve-glue additions (task curve-glue, 2026-11-13)

Everything above is `scratch/curve-facts/CurveFacts.lean` verbatim (its `#print axioms` lines
dropped). Below: `scratch/curve-glue/C2K.lean` §1-§4 (C2K from the leaf `GlobalFunctionsConst`)
and `scratch/curve-glue/C3K.lean` §1-§2 (C3K from the glue `ImagePlaneCurve`, or from C2K and
`ImagePlaneCurveClosed`, and Lean-proved algebra), then the composites. -/

open Opposite TopologicalSpace

"""
final = """
/-- **Both curve facts of mobius-glue from C1b (`SmoothStalkDimOne`, glue, task
infra-smooth-dim), the textbook leaf (L) `GlobalFunctionsConst` and the glue (G1)
`ImagePlaneCurve`.** -/
theorem curveFacts_of_glue (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurve) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_leaves h1 (constOrOntoAlgClosed_of hL) (ratFactorAlgClosed_of hG)

/-- **The same with (G1') `ImagePlaneCurveClosed` (affine image Zariski closed) for (G1).** -/
theorem curveFacts_of_glue' (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurveClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue h1 hL (imagePlaneCurve_of (constOrOntoAlgClosed_of hL) hG)

"""
body = cf_head[len(cf_imports):]
cga = imports + body + note + c2_body + c3_body + final + ENDMARK + """
#print axioms LeafQM.AV.Pin.constOrOntoAlgClosed_of
#print axioms LeafQM.AV.Pin.ratFactorAlgClosed_of
#print axioms LeafQM.AV.Pin.curveFacts_of_glue
#print axioms LeafQM.AV.Pin.curveFacts_of_glue'
"""
open(D + 'CurveGlueAll.lean', 'w').write(cga)

# ---------- MobiusEnd ----------
txt = rd('scratch/mobius-glue/MobiusGlue.lean')
i_s0 = txt.index('/-! ## §0 The definitions of qm-pin')
i_s1 = txt.index('/-! ## §1 Rational functions on `P¹`')
i_s6 = txt.index('/-! ## §6 Downstream')
i_end1 = txt.index('end Pin\n\nend AV\n\nend LeafQM\n', i_s6)
i_samecurves = txt.index('/-- **The comparison of two triples from the curve facts and T5.** -/')
pre = txt[:i_s0]
part1 = txt[i_s1:i_s6]
part2 = txt[i_end1:i_samecurves]
old = "  obtain ⟨⟨hprop', hsmooth', hne', -, -⟩, -⟩ := h1'"
assert part1.count(old) == 1
part1 = part1.replace(old, "  obtain ⟨hprop', hsmooth', hne', -, -, -⟩ := h1'")
pre = pre.replace('import ZInQKernel.HDecomp.QM.Leaves\n', 'import ZInQKernel.HDecomp.QM.Pin\n')
pre = pre.replace('import ZInQKernel.HDecomp.Textbook.SkolemNoether\n',
  'import ZInQKernel.HDecomp.Textbook.SkolemNoether\nimport Mathlib.LinearAlgebra.Lagrange\n'
  'import Mathlib.RingTheory.Polynomial.Resultant.Basic\nimport Mathlib.RingTheory.Polynomial.GaussLemma\n'
  'import Mathlib.FieldTheory.Separable\nimport Mathlib.FieldTheory.IsAlgClosed.Basic\n')
j1 = cga.index('/-! ## §1 Geometric components (genuine definitions) -/')
jend = cga.index(ENDMARK)
cg = cga[j1:jend]
cm = rd(D + 'CMPoints.lean')
cmbody = cm[cm.index('namespace CurveGlue'):cm.index('end CurveGlue')] + 'end CurveGlue\n'
me = pre + ("/-! (curve-glue: §0 of mobius-glue dropped; the kernel's `ZInQKernel/HDecomp/QM/Pin.lean`\n"
  "provides `MobiusGlue`, `R1fpProps` etc. One line of `mobiusGlue_of_curveFacts` changed: the\n"
  "destructuring of `h1' : R1fpProps Y' Φ'` (kernel clause order).) -/\n\n") + part1 + part2
me += """end Pin

end AV

end LeafQM

/-! # curve-glue: curve-facts (verbatim, without its §0 copies) and the C2K/C3K reductions -/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits
open PkgI3

""" + cg + """/-- **The kernel's `MobiusGlue` from C1b, the leaf (L), the glue (G1) and the textbook leaf T5.** -/
theorem mobiusGlue_of_glue (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurve) (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_curves (curveFacts_of_glue h1 hL hG).1 (curveFacts_of_glue h1 hL hG).2 hT

end Pin

""" + cmbody + """
namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits Pin

/-- **End to end: the CM-free form of `MobiusGlue` from the leaf bundle and the named pieces.** -/
theorem mobiusGlueNoCM_of_glue (h1 : SmoothStalkDimOne) (hL : GlobalFunctionsConst)
    (hG : ImagePlaneCurve) (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_glue h1 hL hG hT) h

end CurveGlue

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.mobiusGlue_of_curves
#print axioms LeafQM.AV.Pin.curveFacts_of_glue
#print axioms LeafQM.AV.Pin.mobiusGlue_of_glue
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_glue
"""
open(D + 'MobiusEnd.lean', 'w').write(me)

# ---------- MobiusFinal ----------
inf = rd('scratch/infra-smooth-dim/SmoothDimProps.lean')
infra = inf[inf.index('open Ideal IsLocalRing\n\nnamespace InfraSmoothDim'):inf.index('/-! ## §5 The glue Props (statements copied verbatim) -/')]
pr0 = inf.index('/-- **`SmoothStalkDimOne` holds** (task infra-smooth-dim). -/')
proof = inf[pr0:inf.index('end Pin', pr0)]
l0 = rd(D + 'L0.lean')
l0blk = l0[l0.index('/-! ## The leaf (L0) and the reduction -/'):l0.index('end Pin\n\nend AV')]
mf = 'import Mathlib\n' + me
k = mf.index('noncomputable section\n')
mf = mf[:k] + ("/-! # curve-glue: dimension theory from `scratch/infra-smooth-dim/SmoothDimProps.lean` (its lines\n"
  "from `open Ideal IsLocalRing` to the end of §4, verbatim, inside a section) -/\n\nsection InfraCopy\n\n") \
  + infra + "end InfraCopy\n\n" + mf[k:]
anchor = "/-- **The kernel's `MobiusGlue` from C1b, the leaf (L), the glue (G1) and the textbook leaf T5.** -/"
assert mf.count(anchor) == 1
mf = mf.replace(anchor, l0blk + proof + """/-- **Both curve facts from the leaf (L) and the glue (G1) alone** (C1b proved by
infra-smooth-dim). -/
theorem curveFacts_of_L_G1 (hL : GlobalFunctionsConst) (hG : ImagePlaneCurve) :
    CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue smoothStalkDimOne hL hG

/-- **Both curve facts from (L0) and (G1).** -/
theorem curveFacts_of_L0_G1 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurve) :
    CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_L_G1 (globalFunctionsConst_of hL0) hG

/-- **Both curve facts from (L0) and (G1').** -/
theorem curveFacts_of_L0_G1' (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurveClosed) :
    CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_glue' smoothStalkDimOne (globalFunctionsConst_of hL0) hG

""" + anchor)
tail = "end CurveGlue\n\nend AV\n\nend LeafQM\n\nend\n"
assert mf.count(tail) == 1
mf = mf.replace(tail, """end CurveGlue

namespace CurveGlue

open CategoryTheory AlgebraicGeometry Limits Pin

/-- **The kernel's `MobiusGlue` from the textbook leaf (L) `GlobalFunctionsConst`, the glue (G1)
`ImagePlaneCurve` and the textbook leaf T5 `ObjBridge.TorsionStructure`.** -/
theorem mobiusGlue_of_L_G1_T5 (hL : GlobalFunctionsConst) (hG : ImagePlaneCurve)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_glue smoothStalkDimOne hL hG hT

/-- **The CM-free form, with the CM objects from the leaf bundle `R1R2fp`.** -/
theorem mobiusGlueNoCM_of_L_G1_T5 (hL : GlobalFunctionsConst) (hG : ImagePlaneCurve)
    (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L_G1_T5 hL hG hT) h

/-- **The kernel's `MobiusGlue` from the finiteness theorem (L0) `FiniteGlobalSections`, the glue
(G1) `ImagePlaneCurve` and the textbook leaf T5 `ObjBridge.TorsionStructure`.** -/
theorem mobiusGlue_of_L0_G1_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurve)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_L_G1_T5 (globalFunctionsConst_of hL0) hG hT

/-- **The CM-free form, with the CM objects from the leaf bundle `R1R2fp`.** -/
theorem mobiusGlueNoCM_of_L0_G1_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurve)
    (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L0_G1_T5 hL0 hG hT) h

/-- **Main result: the kernel's `MobiusGlue` from (L0) `FiniteGlobalSections`, (G1')
`ImagePlaneCurveClosed` and T5 `ObjBridge.TorsionStructure`.** -/
theorem mobiusGlue_of_L0_G1'_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurveClosed)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_L0_G1_T5 hL0
    (imagePlaneCurve_of (constOrOntoAlgClosed_of (globalFunctionsConst_of hL0)) hG) hT

/-- **The CM-free form of the main result.** -/
theorem mobiusGlueNoCM_of_L0_G1'_T5 (hL0 : FiniteGlobalSections) (hG : ImagePlaneCurveClosed)
    (hT : ObjBridge.TorsionStructure) (h : R1R2fp) : MobiusGlueNoCM :=
  mobiusGlue_noCM_of (mobiusGlue_of_L0_G1'_T5 hL0 hG hT) h

end CurveGlue

end AV

end LeafQM

end
""")
mf += """#print axioms LeafQM.AV.Pin.smoothStalkDimOne
#print axioms LeafQM.AV.Pin.globalFunctionsConst_of
#print axioms LeafQM.AV.Pin.curveFacts_of_L0_G1
#print axioms LeafQM.AV.Pin.curveFacts_of_L0_G1'
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_L_G1_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_L0_G1_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_G1_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_L0_G1'_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlueNoCM_of_L0_G1'_T5
"""
open(D + 'MobiusFinal.lean', 'w').write(mf)
print('ok')
