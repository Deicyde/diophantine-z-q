#!/usr/bin/env python3
"""QMFull.lean = imports + QMEmb.lean body (QMCorr.lean + part_emb.lean) + part_desc.lean."""
D='scratch/height-glue/'
q=[l for l in open(D+'QMCorr.lean').read().split('\n') if not l.startswith('#print') and not l.startswith('import ')]
e=open(D+'part_emb.lean').read()
d=open(D+'part_desc.lean').read()
hdr='import ZInQKernel.HDecomp.QM.Leaves\nimport ZInQKernel.HDecomp.LeafPush2.T\nimport ZInQKernel.Contrib.AbVarBC.Dim\n'
pr=open(D+'prints_full.lean').read() if __import__('os').path.exists(D+'prints_full.lean') else ''
open(D+'QMFull.lean','w').write(hdr+'\n'.join(q)+e+d+pr)
