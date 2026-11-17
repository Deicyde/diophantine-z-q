import json, copy, sys, time
sys.path.insert(0, __file__.rsplit('/',1)[0])
from lp import solve
from variants import d0, inline, gate_expr, cid, row, hsub
from fractions import Fraction as Fr

def gates(d):
    out={}
    for c in d['coordinates']:
        try:
            expr,rn=gate_expr(d,c['name'])
            if all(len(t['monomial'])<=2 for t in expr): out[c['name']]=(expr,rn)
        except KeyError: pass
    return out
def candidates(d, G):
    names={c['id']:c['name'] for c in d['coordinates']}
    out=[]
    for r in d['residuals']:
        for t in r['terms']:
            if len(t['monomial'])==1:
                g=names[t['monomial'][0]]
                if g in G and G[g][1]!=r['name']: out.append((r['name'],g))
    return out
if __name__=='__main__':
    d=hsub() if 'h' in sys.argv[1:] else copy.deepcopy(d0)
    G=gates(d)
    base,_,rd=solve(d,verbose=False); print('base',base, Fr(base).limit_denominator(1000))
    # only rows that bind or are near anchor chain
    applied=[]
    for it in range(10):
        _,_,rd=solve(d,verbose=False)
        bind={d['residuals'][j]['name'] for j in rd}
        cands=[c for c in candidates(d,G) if c[0] in bind]
        best=None
        for rn,g in cands:
            dd=copy.deepcopy(d); inline(dd,rn,g)
            v,_,_=solve(dd,verbose=False)
            if v<base-1e-9 and (best is None or v<best[0]): best=(v,rn,g)
        print('iter',it,'cands',len(cands),'best',best, flush=True)
        if not best: break
        base=best[0]; inline(d,best[1],best[2]); applied.append(best[1:])
    print('applied',applied, 'final', base, Fr(base).limit_denominator(1000))
    json.dump(applied,open('greedy_applied.json','w'))
    solve(d)
