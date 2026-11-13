#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/HeightBCGlue.lean: StalkPullback body + local_structure part +
verbatim scratch/height-bc/Final.lean (after its import) + bc_proof.lean.part (CotangentSpanBC) +
ula_proof.lean.part (UniformizationLiftAnalytic) + hbc_final.lean.part. Run from repo root."""
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
ls=open(d+'local_structure.lean.part').read().replace('#print axioms AlgebraicGeometry.exists_localStructure_pullback','')
fin=open('scratch/height-bc/Final.lean').read().split('\n')
assert fin[0].startswith('import ZInQKernel')
rest='\n'.join(fin[1:])
opens='''namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
'''
out=[fin[0],'import Mathlib','',
 '/-! # infra-stalks: height-bc glue `CotangentSpanBC` and `UniformizationLiftAnalytic` proved',
 'Part 1: general lemmas (`StalkPullback.lean`, `local_structure.lean.part`). Part 2: verbatim',
 '`scratch/height-bc/Final.lean` (after its import). Part 3: `bc_proof.lean.part`,',
 '`ula_proof.lean.part`, `hbc_final.lean.part`. -/','',
 body,'',ls,'',rest,'',opens,open(d+'bc_proof.lean.part').read(),'',
 open(d+'ula_proof.lean.part').read(),'',open(d+'hbc_final.lean.part').read()]
open(d+'HeightBCGlue.lean','w').write('\n'.join(out))
