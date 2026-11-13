#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/CotangentBaseChange.lean (Mathlib-only): StalkPullback.lean body +
stalk_tensor.lean.part + cot_bc.lean.part. Run from repo root."""
import re
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
st=open(d+'stalk_tensor.lean.part').read()
st='\n'.join(l for l in st.split('\n') if not l.startswith('#print'))
out=['import Mathlib','',
 '/-! # Cotangent space of a base change by a field extension (Mathlib-only)',
 'Assembled by `assemble_cbc.py` from `StalkPullback.lean`, `stalk_tensor.lean.part` and',
 '`cot_bc.lean.part`. -/','',
 body,'',st,'',open(d+'cot_bc.lean.part').read()]
open(d+'CotangentBaseChange.lean','w').write('\n'.join(out))
