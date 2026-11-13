#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/LocalStructure.lean (Mathlib-only): StalkPullback.lean body +
local_structure.lean.part. Run from repo root."""
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
out=['import Mathlib','',
 '/-! # Local structure of fibre products at field-valued points (Mathlib-only)',
 'Assembled by `assemble_ls.py` from `StalkPullback.lean` and `local_structure.lean.part`. -/','',
 body,'',open(d+'local_structure.lean.part').read()]
open(d+'LocalStructure.lean','w').write('\n'.join(out))
