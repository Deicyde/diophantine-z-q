import json,sys
from fractions import Fraction as Fr
def load(p):
    d=json.load(open(p)); names={c['id']:c['name'] for c in d['coordinates']}
    rows={r['name']:{(t['sPower'],tuple(sorted(names[i] for i in t['monomial']))):Fr(t['coefficient']) for t in r['terms']} for r in d['residuals']}
    def conv(x,k=None):
        if k=='monomial': return sorted(names[i] for i in x)
        if isinstance(x,list): return [conv(v) for v in x]
        if isinstance(x,dict): return {kk:conv(v,kk) for kk,v in x.items() if kk!='sourceLines'}
        return x
    return rows,conv(d['guards'])
a,ga=load(sys.argv[1]); b,gb=load(sys.argv[2])
print('deleted',sorted(a.keys()-b.keys())); print('added',sorted(b.keys()-a.keys()))
print('changed',sorted(n for n in a.keys()&b.keys() if a[n]!=b[n])); print('guards equal',ga==gb, 'rows common unchanged', sum(a[n]==b[n] for n in a.keys()&b.keys()))
