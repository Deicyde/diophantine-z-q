#!/usr/bin/env python3
"""QMEmb.lean = QMCorr.lean (without its axiom check) + part_emb.lean (+ axiom checks)."""
D='scratch/height-glue/'
q=[l for l in open(D+'QMCorr.lean').read().split('\n') if not l.startswith('#print')]
e=open(D+'part_emb.lean').read()
pr=open(D+'prints_emb.lean').read() if __import__('os').path.exists(D+'prints_emb.lean') else ''
open(D+'QMEmb.lean','w').write('\n'.join(q)+e+pr)
