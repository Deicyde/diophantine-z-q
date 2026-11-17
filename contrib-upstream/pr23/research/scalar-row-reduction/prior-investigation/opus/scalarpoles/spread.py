import json,sys
from fractions import Fraction as F
def spreads(ir,w):
    d=json.load(open(ir)); nm={c['id']:c['name'] for c in d['coordinates']}
    out=[]
    for r in d['residuals']:
        ps=[6*t['sPower']+sum(w.get(nm[i],0) for i in t['monomial']) for t in r['terms']]
        # 3-adic size of coefficients ignored; spread in units of c
        out.append((max(ps)-min(ps),r['name']))
    return sorted(out,reverse=True)
if __name__=='__main__':
    w=json.load(open(sys.argv[2]))['three']
    for s in spreads(sys.argv[1],w)[:8]: print(s)
