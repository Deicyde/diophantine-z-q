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
