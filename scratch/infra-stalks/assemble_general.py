#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/CotangentPullback.lean (Mathlib-only): StalkPullback.lean +
CotangentProduct.lean bodies + cot_pullback.lean.part. Run from repo root."""
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
cp=open(d+'CotangentProduct.lean').read()
cpbody=cp[cp.index('namespace IsLocalRing'):]
out=['import Mathlib','',
 '/-! # Cotangent spaces of fibre products (Mathlib-only)',
 'Assembled by `assemble_general.py` from `StalkPullback.lean`, `CotangentProduct.lean` and',
 '`cot_pullback.lean.part` (scratch files cannot import each other). New results:',
 '`AlgebraicGeometry.cotangent_span_pullback` (base change by a point with field stalk) and',
 '`AlgebraicGeometry.sub_mem_sq_pairPt` (product at a pair of section points). -/','',
 body,'',cpbody,'',open(d+'cot_pullback.lean.part').read()]
open(d+'CotangentPullback.lean','w').write('\n'.join(out))
