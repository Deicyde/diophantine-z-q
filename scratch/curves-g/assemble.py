"""curves-g: build the single-file check scratch/curves-g/CurvesG3.lean (not committed; regenerate).
= leaf-fold3's flat file scratch/leaf-fold3/Leaves3.lean (verbatim)
+ part_g3.lean, generated here from:
  - the bodies of ZInQKernel/Contrib/CurvesG/RatPoint.lean, CurveSplit.lean and GenusSplit.lean (verbatim, between their
    `namespace ZInQ.Contrib.CurvesG` and `end ZInQ.Contrib.CurvesG`), placed in `namespace HDec.CurvesG3`
    so that `LeafModCurves`, `X1Belyi`, `PkgI3` resolve to the flat file's copies, as in its other parts;
  - the field lines of d90's `OpenTextbookLeaves3` (verbatim, from scratch/leaf-fold3/partsF/d90_fold3.lean)
    with `t34`, `t38` replaced by the curves-g leaves, and the fold theorem.
Run from the repository root: python3 scratch/curves-g/assemble.py"""
import re
R = 'scratch/curves-g/'
def body(path):
    s = open(path).read()
    b = s[s.index('namespace ZInQ.Contrib.CurvesG\n') + len('namespace ZInQ.Contrib.CurvesG\n'):
          s.index('end ZInQ.Contrib.CurvesG')]
    return b
d90 = open('scratch/leaf-fold3/partsF/d90_fold3.lean').read()
st = d90[d90.index('structure OpenTextbookLeaves3 : Prop where\n'):]
st = st[:st.index('\n\n')]
fields = st.split('\n')[1:]
assert any(l == '  t34 : LeafModCurves.DimJ1Genus' for l in fields)
assert any(l == '  t38 : X1Belyi.CurveOfFunctionFieldQ' for l in fields)
newf = []
for l in fields:
    if l == '  t34 : LeafModCurves.DimJ1Genus':
        newf += ['  /-- T34, first half (curves-g): `dim Jac X = g(X)`. -/',
                 '  t34a : CurvesG3.DimJacobianEqGenus',
                 '  /-- T34, second half (curves-g): `g(K_N) = genus Γ₁(N)`. -/',
                 '  t34b : CurvesG3.GenusX1Field']
    elif l == '  t38 : X1Belyi.CurveOfFunctionFieldQ':
        newf += ['  /-- T38 (A) (curves-g): the normal proper model of a function field. -/',
                 '  t38a : CurvesG3.NormalModelOfFunctionFieldQ',
                 '  /-- T38 (B) (curves-g): normal curves over `ℚ` are smooth. -/',
                 '  t38b : CurvesG3.NormalCurveSmoothQ',
                 '  /-- T38 (C) (curves-g): constant field `ℚ` gives geometric connectedness. -/',
                 '  t38c : CurvesG3.GeomConnectedOfConstantFieldQ']
    else:
        newf.append(l)
names = [m.group(1) for l in fields for m in [re.match(r'  (\w+) :', l)] if m]
assigns = []
for n in names:
    if n == 't34': assigns.append('  t34 := CurvesG3.dimJ1Genus_of_split t.t34a t.t34b')
    elif n == 't38': assigns.append('  t38 := CurvesG3.curveOfFunctionFieldQ_of_split t.t38a t.t38b t.t38c')
    else: assigns.append(f'  {n} := t.{n}')
part = f'''
/-! ## curves-g (part g3): T38's point clause proved, T38 and T34 split; leaf-fold3's bundle refolded -/

namespace HDec

namespace CurvesG3

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory LeafModCurves X1Belyi

noncomputable section
{body('ZInQKernel/Contrib/CurvesG/RatPoint.lean')}
{body('ZInQKernel/Contrib/CurvesG/CurveSplit.lean')}
{body('ZInQKernel/Contrib/CurvesG/GenusSplit.lean')}
end

end CurvesG3

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

/-- **leaf-fold3's `OpenTextbookLeaves3` with `t34` and `t38` split** (curves-g). -/
structure OpenTextbookLeavesG : Prop where
''' + '\n'.join(newf) + '''

/-- The curves-g bundle gives leaf-fold3's bundle. -/
theorem textbookLeaves3_of_G (t : OpenTextbookLeavesG) : OpenTextbookLeaves3 where
''' + '\n'.join(assigns) + '''

/-- **`SixContactMin` from the curves-g bundle** (leaf-fold3's `sixContactMin_of_open3`). -/
theorem sixContactMin_of_openG (r : OpenResearchLeaves2) (t : OpenTextbookLeavesG)
    (l : OpenAddedLeaves3) (g : OpenGlue3) : ZInQ.SixContactMin :=
  sixContactMin_of_open3 r (textbookLeaves3_of_G t) l g

/-- The proved types are the bundle's field types (the flat file's own `t34`, `t38` Props). -/
example : CurvesG3.CurveOfFunctionFieldQNoPoint → X1Belyi.CurveOfFunctionFieldQ :=
  CurvesG3.curveOfFunctionFieldQ_of_noPoint
example : CurvesG3.NormalModelOfFunctionFieldQ → CurvesG3.NormalCurveSmoothQ →
    CurvesG3.GeomConnectedOfConstantFieldQ → X1Belyi.CurveOfFunctionFieldQ :=
  CurvesG3.curveOfFunctionFieldQ_of_split
example : CurvesG3.DimJacobianEqGenus → CurvesG3.GenusX1Field → LeafModCurves.DimJ1Genus :=
  CurvesG3.dimJ1Genus_of_split

end HSyn

end HDec

example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_openG

#print axioms HDec.CurvesG3.nonempty_ratPt_of_place
#print axioms HDec.CurvesG3.curveOfFunctionFieldQ_of_noPoint
#print axioms HDec.CurvesG3.curveOfFunctionFieldQNoPoint_of_split
#print axioms HDec.CurvesG3.curveOfFunctionFieldQ_of_split
#print axioms HDec.CurvesG3.dimJ1Genus_of_split
#print axioms HDec.HSyn.textbookLeaves3_of_G
#print axioms HDec.HSyn.sixContactMin_of_openG
'''
open(R + 'part_g3.lean', 'w').write(part)
flat = open('scratch/leaf-fold3/Leaves3.lean').read()
open(R + 'CurvesG3.lean', 'w').write(flat.rstrip('\n') + '\n' + part)
print('wrote', R + 'part_g3.lean', len(part.splitlines()), 'lines;', R + 'CurvesG3.lean',
      len(flat.splitlines()) + len(part.splitlines()), 'lines')
