#!/usr/bin/env python3
"""Assemble scratch/infra-hodge/IntegrationG0Tail.lean: the S-alg proof in g0-assemble2's environment.
Run from the repository root. The file starts with `import TailB` (g0-assemble2's olean chain
LPrefix -> TailA -> TailB, built from VERBATIM copies of scratch/g0-assemble2/olean/{LPrefix,TailA,TailB}.lean
into a /tmp olean directory; TailB contains part a25 = product-height's file over Leaves.lean's
DefFaltings copy), then VERBATIM infra-stalks StalkPullback / CotangentProduct bodies and cot_pullback /
local_structure parts, VERBATIM hodge-bc2 ExtFrac body, and the infra-hodge parts phl_1-3, phl_4a,
ps_1-ps_6 with the line `--IH:ABVAR` dropped (AbVar is def-faltings' copy through `open DefFaltings`,
as in g0-assemble2's a25), each part in its own section.
Check: LEAN_PATH=<olean dir>:$(lake env printenv LEAN_PATH) lean IntegrationG0Tail.lean"""
import os
d='scratch/infra-hodge/'
s='scratch/infra-stalks/'
def noprint(t): return '\n'.join(l for l in t.split('\n') if not l.startswith('#print'))
sp=open(s+'StalkPullback.lean').read(); sp=sp[sp.index('universe u'):]
cp=open(s+'CotangentProduct.lean').read(); cp=cp[cp.index('namespace IsLocalRing'):]
cpp=noprint(open(s+'cot_pullback.lean.part').read())
ls=noprint(open(s+'local_structure.lean.part').read())
ef=open('ZInQKernel/Contrib/HodgeBC2/ExtFrac.lean').read().split('\n',1)[1]
gen=['phl_1_cot.lean.part','phl_2_split.lean.part','phl_3_linalg.lean.part','phl_4a_basis.lean.part']
parts=sorted(f for f in os.listdir(d) if f.startswith('ps_') and f.endswith('.lean.part'))
def sec(n,t): return 'section IHG0_'+n+'\n'+t+'\nend IHG0_'+n
body=[sec(f.split('.')[0], open(d+f).read().replace('--IH:ABVAR','')) for f in gen+parts]
out=['import TailB','','/-! # infra-hodge: S-alg in g0-assemble2\'s environment (see assemble_g0.py) -/','',
  sec('sp',sp),'',sec('cp',cp),'',sec('cpp',cpp),'',sec('ls',ls),'',sec('ef',ef),'']+body+['',
  '/-- The field `productMetrizationOfProductUnif` of g0-assemble2\'s `GluePieces3` is a theorem. -/',
  'theorem HSyn.gluePieces3_productMetrizationOfProductUnif :',
  '    ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=',
  '  ZInQ.InfraHodge.productMetrizationOfProductUnif','',
  '#print axioms HSyn.gluePieces3_productMetrizationOfProductUnif']
open(d+'IntegrationG0Tail.lean','w').write('\n'.join(out))
print('parts:',gen+parts)
