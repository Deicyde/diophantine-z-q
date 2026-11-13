# Generates SmoothStalk.lean and SmoothDimProps.lean from the parts (scratch files cannot import each other).
d='scratch/infra-smooth-dim/'
a=open(d+'StdSmoothLocal.lean').read()
a=a[:a.index('#print axioms')]
b=open(d+'stalk_part.lean.part').read()
open(d+'SmoothStalk.lean','w').write(a.replace("# Local rings of a standard smooth algebra over a field","# Local rings of smooth schemes over a field (§0-§3 = StdSmoothLocal.lean verbatim)",1)+b)
b2=b[:b.index('#print axioms')]
c=open(d+'props_part.lean.part').read()
s=(a+b2).replace("import Mathlib\n","import Mathlib\nimport ZInQKernel.HDecomp.Objects\n",1)
s=s.replace("# Local rings of a standard smooth algebra over a field","# Dimension theory of smooth schemes over a field, and the glue Props (§0-§4 = SmoothStalk.lean verbatim)",1)
open(d+'SmoothDimProps.lean','w').write(s+c)
# HodgeLatticeClosed.lean: imports the kernel's HodgeLattice module (statements not copied, used as is).
g=open('scratch/g0-dim/Dim.lean').read().split('\n')
g0=('\n/-! ## §5 g0-dim §1-§2 (copied verbatim from `scratch/g0-dim/Dim.lean`, lines 107-305) -/\n\n'
    'section G0DimCopy\nset_option linter.style.haveILetI false\nset_option linter.unusedSectionVars false\n'
    'open Order TensorProduct\n\n'+'\n'.join(g[106:305])+'\n\nend G0DimCopy\n')
h=(a+b2).replace("import Mathlib\n","import Mathlib\nimport ZInQKernel.HDecomp.Faltings.HodgeLattice\n",1)
h=h.replace("# Local rings of a standard smooth algebra over a field","# Dimension theory of smooth schemes over a field, and `HodgeLatticeTheorem` closed (§0-§4 = SmoothStalk.lean verbatim)",1)
open(d+'HodgeLatticeClosed.lean','w').write(h+g0+open(d+'closed_part.lean.part').read())
# CurveFactsClosed.lean: curve-facts' CurveFacts.lean (verbatim, minus imports and #print lines), then §0-§4, then curve_part.
cf=open('scratch/curve-facts/CurveFacts.lean').read().split('\n')
body='\n'.join(l for l in cf[2:] if not l.startswith('#print'))
hdr=('import Mathlib\nimport ZInQKernel.HDecomp.QM.Pairs\nimport Mathlib.LinearAlgebra.Lagrange\n\n'
     '/-! # curve-facts with C1b proved (task infra-smooth-dim)\n\n'
     'Part 1: `scratch/curve-facts/CurveFacts.lean` verbatim (without its imports and `#print` lines).\n'
     'Part 2: `SmoothStalk.lean` §0-§4 verbatim. Part 3 (§6): C1b, C1a, C1 proved. -/\n')
s2=(a+b2).replace("import Mathlib\n","",1)
open(d+'CurveFactsClosed.lean','w').write(hdr+body+'\n'+s2+open(d+'curve_part.lean.part').read())
