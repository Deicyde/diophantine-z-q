#!/usr/bin/env python3
"""Assemble the infra-hodge check of `ProductMetrizationOfProductUnif` (product-height, S-alg).
Run from the repository root.

SPrefix.lean:
  * `import ZInQKernel.HDecomp.Faltings.H5Neron` (the only import of product-height's file) and
    `import Mathlib`;
  * VERBATIM bodies of infra-stalks' StalkPullback.lean, CotangentProduct.lean, cot_pullback and
    local_structure parts (`#print` dropped), and of hodge-bc2's ExtFrac.lean;
  * VERBATIM scratch/product-height/ProductHeight.lean after its import line (owner text of
    `ProductMetrizationOfProductUnif`; g0-assemble2's a25_productheight.lean is the same text with
    one `open` line replaced, see verbatim_check.py).
ProductSplit.lean = SPrefix + the generic infra-hodge parts phl_1, phl_2, phl_3, phl_4a + ps_*.lean.part.
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
ph=open('scratch/product-height/ProductHeight.lean').read().split('\n')
assert ph[0]=='import ZInQKernel.HDecomp.Faltings.H5Neron'; ph='\n'.join(ph[1:])
head=['import ZInQKernel.HDecomp.Faltings.H5Neron','import Mathlib','',
 '/-! # infra-hodge: `ProductMetrizationOfProductUnif` (product-height glue S-alg)',
 'Assembled by `scratch/infra-hodge/assemble_split.py`; see its docstring for the verbatim sources. -/','',
 sp,'',cp,'',cpp,'',ls,'',ef,'',ph,'']
prefix='\n'.join(head)
open(d+'SPrefix.lean','w').write(prefix)
gen=['phl_1_cot.lean.part','phl_2_split.lean.part','phl_3_linalg.lean.part','phl_4a_basis.lean.part']
parts=sorted(f for f in os.listdir(d) if f.startswith('ps_') and f.endswith('.lean.part'))
open(d+'ProductSplit.lean','w').write(prefix+'\n'+'\n\n'.join(open(d+f).read().replace('--IH:ABVAR','open PkgI3 (AbVar)') for f in gen+parts))
print('parts:',gen+parts)
