#!/usr/bin/env python3
"""Assemble the hodge-bc2 single-file checks. Run from the repository root.

HBCPrefix.lean (development prefix, also the head of every check):
  * `import ZInQKernel.HDecomp.Faltings.Leaves`, `import Mathlib` (as infra-stalks' files);
  * VERBATIM body of scratch/infra-stalks/CotangentBaseChange.lean (from `universe u`):
    stalks of fibre products, `cotangent_baseChange_injective`;
  * scratch/hodge-bc2/ExtFrac.lean body (new, Mathlib-only);
  * VERBATIM lines of scratch/height-bc/Final.lean: 29-34 (namespace, opens), 590-858 (natural map
    of a base change: bO ... bcHodge_wedge), then `end Construction`; 1747-1757 (`CotangentSpanBC`);
    1453-1465 (`HodgeBCInjective`);
  * VERBATIM scratch/infra-stalks/bc_proof.lean.part (proof of `CotangentSpanBC`), `#print` dropped.
HodgeBCInjective.lean = HBCPrefix + hbc_proof.lean.part (new).
"""
import sys
d='scratch/hodge-bc2/'
def noprint(s): return '\n'.join(l for l in s.split('\n') if not l.startswith('#print'))
cbc=open('scratch/infra-stalks/CotangentBaseChange.lean').read()
cbc=cbc[cbc.index('universe u'):]
ef=open(d+'ExtFrac.lean').read()
ef=ef[ef.index('namespace ZInQ.HodgeBC2')-len('/-! # Exterior'):] if False else ef[ef.index('/-! # Exterior'):]
fin=open('scratch/height-bc/Final.lean').read().split('\n')
def L(a,b): return '\n'.join(fin[a-1:b])
assert fin[1452].startswith('/-- **Glue BC-alg'), fin[1452]
assert fin[1458].startswith('def HodgeBCInjective'), fin[1458]
assert fin[1746].startswith('/-- **Glue BC-cot'), fin[1744]
assert fin[1751].startswith('def CotangentSpanBC')
assert fin[857].startswith('omit [NumberField L]'), fin[857]
bcp=noprint(open('scratch/infra-stalks/bc_proof.lean.part').read())
head=['import ZInQKernel.HDecomp.Faltings.Leaves','import Mathlib','',
 '/-! # hodge-bc2: `HodgeBCInjective` (height-bc glue)',
 'Assembled by `scratch/hodge-bc2/assemble.py`; see its docstring for the verbatim sources. -/','',
 cbc,'',ef,'',L(29,34),'',L(590,856),'','end Construction','',L(1747,1757),'',L(1453,1465),'',bcp]
prefix='\n'.join(head)
open(d+'HBCPrefix.lean','w').write(prefix)
import os
if os.path.exists(d+'hbc_proof.lean.part'):
  open(d+'HodgeBCInjective.lean','w').write(prefix+'\n\n'+open(d+'hbc_proof.lean.part').read())
