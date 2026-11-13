#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/UniformizationLift.lean: StalkPullback body + local_structure part +
verbatim scratch/height-bc/Final.lean (after its import) + ula_proof.lean.part. Run from repo root."""
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
ls=open(d+'local_structure.lean.part').read().replace('#print axioms AlgebraicGeometry.exists_localStructure_pullback','')
fin=open('scratch/height-bc/Final.lean').read().split('\n')
assert fin[0].startswith('import ZInQKernel')
rest='\n'.join(fin[1:])
out=[fin[0],'import Mathlib','',
 '/-! # infra-stalks: `UniformizationLiftAnalytic` (height-bc) proved',
 'Part 1: general lemmas (`StalkPullback.lean`, `local_structure.lean.part`). Part 2: verbatim',
 '`scratch/height-bc/Final.lean` (after its import). Part 3: `ula_proof.lean.part`. -/','',
 body,'',ls,'',rest,'',open(d+'ula_proof.lean.part').read()]
open(d+'UniformizationLift.lean','w').write('\n'.join(out))
