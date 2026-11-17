import json, sys, copy
sys.path.insert(0, __file__.rsplit('/',1)[0])
from lp import solve
from fractions import Fraction as Fr
def key(t): return (Fr(t['sPower']), tuple(sorted(t['monomial'])))
def addrow(d, i, j, lam):
    acc={}
    for t in d['residuals'][i]['terms']: acc[key(t)]=acc.get(key(t),0)+Fr(t['coefficient'])
    for t in d['residuals'][j]['terms']: acc[key(t)]=acc.get(key(t),0)+lam*Fr(t['coefficient'])
    d['residuals'][i]['terms']=[{'sPower':str(s) if s.denominator!=1 else int(s),'monomial':list(m),'coefficient':str(c)} for (s,m),c in acc.items() if c]
def moves(d, i):
    ri=d['residuals'][i]; mi={tuple(sorted(t['monomial'])):t for t in ri['terms']}
    out=[]
    for j,rj in enumerate(d['residuals']):
        if j==i: continue
        for t in rj['terms']:
            m=tuple(sorted(t['monomial']))
            if m in mi and m!=() and Fr(t['sPower'])==Fr(mi[m]['sPower']):
                out.append((j, -Fr(mi[m]['coefficient'])/Fr(t['coefficient'])))
    return out
if __name__=='__main__':
    d=json.load(open(sys.argv[1])); out=sys.argv[2]
    base,_,rd=solve(d,verbose=False); print('base',base,flush=True); hist=[]
    for it in range(int(sys.argv[3]) if len(sys.argv)>3 else 8):
        _,_,rd=solve(d,verbose=False); best=None
        for i in rd:
            for j,lam in moves(d,i):
                dd=copy.deepcopy(d); addrow(dd,i,j,lam)
                v,_,_=solve(dd,verbose=False)
                if v<base-1e-7 and (best is None or v<best[0]): best=(v,i,j,lam)
        if not best: print('no improving single row op'); break
        v,i,j,lam=best; addrow(d,i,j,lam); base=v
        hist.append((d['residuals'][i]['name'],d['residuals'][j]['name'],str(lam),v))
        print('iter',it,hist[-1],Fr(v).limit_denominator(5000),flush=True)
    json.dump(d,open(out,'w')); json.dump(hist,open(out+'.hist','w'),indent=1)
    solve(d)
