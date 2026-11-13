#!/usr/bin/env python3
"""Assemble scratch/infra-stalks/CotangentSpanBC.lean from StalkPullback.lean (general lemmas),
verbatim lines of scratch/height-bc/Final.lean (Part B construction + CotangentSpanBC), and
bc_proof.lean.part. Run from the repository root."""
import re
d='scratch/infra-stalks/'
sp=open(d+'StalkPullback.lean').read()
body=sp[sp.index('universe u'):]
fin=open('scratch/height-bc/Final.lean').read().split('\n')
def L(a,b): return '\n'.join(fin[a-1:b])
out=['import ZInQKernel.HDecomp.Faltings.Leaves','import Mathlib','',
 '/-! # infra-stalks: `CotangentSpanBC` (height-bc) proved',
 'Part 1: general lemmas copied from `StalkPullback.lean`. Part 2: verbatim lines 29-34, 590-763',
 'and 1745-1757 of `scratch/height-bc/Final.lean` (natural map of a base change; `CotangentSpanBC`).',
 'Part 3: the proof (`bc_proof.lean.part`). -/','',
 body,'',L(29,34),'',L(590,763),'','end Construction','',L(1747,1757),'',
 open(d+'bc_proof.lean.part').read()]
open(d+'CotangentSpanBC.lean','w').write('\n'.join(out))
