#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/MulKer.lean: StalkPullback.lean body (general lemmas) + verbatim
scratch/mul-rigidity/Mul.lean (after its imports) + ker_proof.lean.part. Run from repo root."""
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
mul=open('scratch/mul-rigidity/Mul.lean').read().split('\n')
imports=[l for l in mul[:12] if l.startswith('import')]
rest='\n'.join(mul[len(imports):])
out=imports+['import Mathlib','',
 '/-! # infra-stalks: `KerUnitOpenOfCotangentSurj` (mul-rigidity) proved',
 'Part 1: general lemmas copied from `StalkPullback.lean`. Part 2: verbatim',
 '`scratch/mul-rigidity/Mul.lean` (after its imports). Part 3: `ker_proof.lean.part`. -/','',
 body,'',rest,'',open(d+'ker_proof.lean.part').read()]
open(d+'MulKer.lean','w').write('\n'.join(out))
