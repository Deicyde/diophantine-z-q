#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/StalkTensor.lean (Mathlib-only): StalkPullback.lean body +
stalk_tensor.lean.part. Run from repo root."""
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
out=['import Mathlib','',
 '/-! # Stalks of fibre products as localizations of tensor products of stalks (Mathlib-only)',
 'Assembled by `assemble_st.py` from `StalkPullback.lean` and `stalk_tensor.lean.part`. -/','',
 body,'',open(d+'stalk_tensor.lean.part').read()]
open(d+'StalkTensor.lean','w').write('\n'.join(out))
