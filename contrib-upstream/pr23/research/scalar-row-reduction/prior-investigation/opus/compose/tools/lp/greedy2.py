import json, copy, sys, re
sys.path.insert(0, __file__.rsplit('/',1)[0])
from lp import solve
from variants import d0, inline, gate_expr, cid, row, hsub
from greedy import gates
from fractions import Fraction as Fr
def moves(d,G,bind):
    names={c['id']:c['name'] for c in d['coordinates']}
    mv={}
    for r in d['residuals']:
        if r['name'] not in bind: continue
        sib=re.sub(r'\.(\d)$','',r['name'])
        lin=[names[t['monomial'][0]] for t in r['terms'] if len(t['monomial'])==1 and names[t['monomial'][0]] in G and G[names[t['monomial'][0]]][1]!=r['name']]
        for g in lin:
            gb=re.sub(r'\.(\d)(\.quadratic)?$','',g)
            mv.setdefault((sib,gb),set()).add((r['name'],g))
    # expand to siblings
    out=[]
    for (sib,gb),s in mv.items():
        pairs=set()
        for r in d['residuals']:
            if re.sub(r'\.(\d)$','',r['name'])==sib:
                for t in r['terms']:
                    if len(t['monomial'])==1:
                        g=names[t['monomial'][0]]
                        if g in G and re.sub(r'\.(\d)(\.quadratic)?$','',g)==gb and G[g][1]!=r['name']: pairs.add((r['name'],g))
        out.append(sorted(pairs))
    return out
if __name__=='__main__':
    d=copy.deepcopy(d0)
    G=gates(d)
    base,_,_=solve(d,verbose=False); applied=[]
    for it in range(15):
        _,_,rd=solve(d,verbose=False)
        bind={d['residuals'][j]['name'] for j in rd}
        best=None
        for mvset in moves(d,G,bind):
            dd=copy.deepcopy(d)
            for rn,g in mvset: inline(dd,rn,g)
            v,_,_=solve(dd,verbose=False)
            if v<base-1e-9 and (best is None or v<best[0]): best=(v,mvset)
        print('iter',it,'best',best and (best[0],Fr(best[0]).limit_denominator(2000),best[1]), flush=True)
        if not best: break
        base=best[0]
        for rn,g in best[1]: inline(d,rn,g)
        applied+=best[1]
    json.dump(applied,open('greedy2_applied.json','w'),indent=1)
    json.dump(d,open('greedy2_ir.json','w'))
    solve(d)
