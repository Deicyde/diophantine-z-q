#!/usr/bin/env python3
"""Assemble scratch/height-glue/HeightGlue.lean (scratch files cannot import each other).
Sources, verbatim: base/Kernel_metrization2.lean (= scratch/metrization2/Kernel.lean, task
metrization2), base/JacDescends_unifdims.lean (extracted from scratch/unif-dims/Combined.lean,
task unif-dims), AUUnique.lean (this task, without its import and final `end`), part_*.lean."""
import sys
D='scratch/height-glue/'
hdr=['import ZInQKernel.HDecomp.LeafPush2.T','import ZInQKernel.Contrib.Dim.HodgeLattice','import ZInQKernel.HDecomp.Faltings.H5Neron','']
k=open(D+'base/Kernel_metrization2.lean').read().split('\n')
k=[l for l in k if not l.startswith('import ') and not l.startswith('#print')]
j=open(D+'base/JacDescends_unifdims.lean').read().split('\n')
a=open(D+'AUUnique.lean').read().split('\n')
a=[l for l in a if not l.startswith('import ') and not l.startswith('#print')]
while a and a[-1].strip()=='': a.pop()
assert a[-1].startswith('end ZInQ.HeightGlue'); a.pop()
parts=sys.argv[1:]
body=[]
for p in parts: body+=open(D+p).read().split('\n')
out=hdr+k+j+a+body+['end ZInQ.HeightGlue','']
prints=[l for l in body if False]
open(D+'HeightGlue.lean','w').write('\n'.join(out)+open(D+'prints.lean').read())
