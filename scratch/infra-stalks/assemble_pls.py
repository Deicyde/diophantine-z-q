#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/ProductLocalStructure.lean: StalkPullback.lean body +
local_structure.lean.part + verbatim scratch/metrization/Metrization.lean (after its import) +
pls_proof.lean.part. Run from repo root."""
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
ls=open(d+'local_structure.lean.part').read()
ls=ls.replace('#print axioms AlgebraicGeometry.exists_localStructure_pullback','')
met=open('scratch/metrization/Metrization.lean').read().split('\n')
assert met[0]=='import Mathlib'
rest='\n'.join(met[1:])
out=['import Mathlib','',
 '/-! # infra-stalks: `ProductLocalStructure` (metrization) proved',
 'Part 1: general lemmas (`StalkPullback.lean`, `local_structure.lean.part`). Part 2: verbatim',
 '`scratch/metrization/Metrization.lean` (after its import). Part 3: `pls_proof.lean.part`. -/','',
 body,'',ls,'',rest,'',open(d+'pls_proof.lean.part').read()]
open(d+'ProductLocalStructure.lean','w').write('\n'.join(out))
