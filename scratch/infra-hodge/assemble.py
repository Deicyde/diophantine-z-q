#!/usr/bin/env python3
"""Assemble the infra-hodge single-file checks. Run from the repository root.

Prefix.lean (head of every check; scratch files cannot import each other):
  * `import Mathlib`;
  * VERBATIM bodies (from `universe u` / `namespace IsLocalRing`) of infra-stalks'
    StalkPullback.lean and CotangentProduct.lean, and VERBATIM cot_pullback.lean.part and
    local_structure.lean.part (`#print` lines dropped): stalks/cotangent spaces of fibre products;
  * VERBATIM body of ZInQKernel/Contrib/HodgeBC2/ExtFrac.lean (hodge-bc2, Mathlib-only);
  * VERBATIM scratch/metrization/Metrization.lean after its `import Mathlib` line (contains the
    owner's text of `ProductHodgeLattice`);
  * VERBATIM scratch/infra-stalks/pls_proof.lean.part (`productLocalStructure`), `#print` dropped.
ProductHodgeLattice.lean = Prefix + the new parts phl_*.lean.part (in order).
"""
import os
d='scratch/infra-hodge/'
s='scratch/infra-stalks/'
def noprint(t): return '\n'.join(l for l in t.split('\n') if not l.startswith('#print'))
sp=open(s+'StalkPullback.lean').read(); sp=sp[sp.index('universe u'):]
cp=open(s+'CotangentProduct.lean').read(); cp=cp[cp.index('namespace IsLocalRing'):]
cpp=noprint(open(s+'cot_pullback.lean.part').read())
ls=noprint(open(s+'local_structure.lean.part').read())
ef=open('ZInQKernel/Contrib/HodgeBC2/ExtFrac.lean').read().split('\n')
assert ef[0]=='import Mathlib'; ef='\n'.join(ef[1:])
met=open('scratch/metrization/Metrization.lean').read().split('\n')
assert met[0]=='import Mathlib'; met='\n'.join(met[1:])
pls=noprint(open(s+'pls_proof.lean.part').read())
head=['import Mathlib','',
 '/-! # infra-hodge: `ProductHodgeLattice` (metrization glue)',
 'Assembled by `scratch/infra-hodge/assemble.py`; see its docstring for the verbatim sources. -/','',
 sp,'',cp,'',cpp,'',ls,'',ef,'',met,'',pls,'']
prefix='\n'.join(head)
open(d+'Prefix.lean','w').write(prefix)
parts=sorted(f for f in os.listdir(d) if f.startswith('phl_') and f.endswith('.lean.part'))
if parts:
  open(d+'ProductHodgeLattice.lean','w').write(prefix+'\n'+'\n\n'.join(open(d+f).read() for f in parts))
print('parts:',parts)
