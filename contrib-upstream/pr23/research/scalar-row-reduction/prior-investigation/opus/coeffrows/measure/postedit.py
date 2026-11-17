"""Post-compile row edits on the pipeline-A final IR: chain f-leaf scaled by S^-p (row multiplied by S^p),
and optional N(f) anchor with S^2. Writes IRs for exact balancing."""
import json, sys, copy
sys.path.insert(0,'lp')
import variants as V
H=json.load(open('runs/vA/final/integer-candidate-ir.json'))
def chain_s(d,p):
    d=copy.deepcopy(d)
    for rn,leaf in [('scalar.chain3.definition','scalar.shiftedS.f.1'),('scalar.chain2.definition','scalar.shiftedS.f.0')]:
        r=V.row(d,rn); lid=V.cid(d,leaf)
        for t in r['terms']:
            if t['monomial']!=[lid,lid]: t['sPower']+=p
    return d
V.d0=H
json.dump(chain_s(H,1),open('runs/postB_S1.json','w'))
json.dump(chain_s(V.fanchor(2),2),open('runs/postC_S2.json','w'))
