"""Generate Deligne.lean = Adelic.lean body + shimura-split's Y3Conn.lean body (verbatim) +
the definition `HDec.QMSplit.Moduli.DeligneComponentsX6` (verbatim from shimura-split's parts/RowsNew.lean)
+ parts/DeligneNew.lean, over the kernel import `ZInQKernel.HDecomp.QM.Leaves`."""
import re
d='scratch/shimura-glue/'
def split(path):
    s=open(path).read()
    imports=[l for l in s.splitlines() if l.startswith('import ')]
    body='\n'.join(l for l in s.splitlines() if not l.startswith('import '))
    return imports, body
ia, ba = split(d+'Adelic.lean')
iy, by_ = split('scratch/shimura-split/Y3Conn.lean')
rows=open('scratch/shimura-split/parts/RowsNew.lean').read()
i=rows.index('/-- **LEAF-form (Deligne\'s components at level one; specialization).**')
j=rows.index('theorem geomConnX6_of')
x6def=rows[i:j]
x6='''namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

'''+x6def+'''end HDec.QMSplit.Moduli
'''
_, bn = split(d+'parts/DeligneNew.lean')
imports=[]
for l in ['import ZInQKernel.HDecomp.QM.Leaves']+ia+iy:
    if l not in imports: imports.append(l)
out='\n'.join(imports)+'\n\n'+ba+'\n\n/-! ## Part 2: shimura-split `Y3Conn.lean`, verbatim -/\n'+by_+ \
  '\n\n/-! ## Part 3: shimura-split `DeligneComponentsX6`, verbatim -/\n\n'+x6+'\n'+bn
open(d+'Deligne.lean','w').write(out)
print('ok', out.count('\n'))
