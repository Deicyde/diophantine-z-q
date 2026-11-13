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
