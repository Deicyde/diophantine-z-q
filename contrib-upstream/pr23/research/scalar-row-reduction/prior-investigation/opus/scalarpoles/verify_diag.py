"""Independent check of a fractional diagonal balance: rows, quartic table, input fixed."""
import json,sys,math
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
sys.set_int_max_str_digits(0)
root=Path(sys.argv[1])
src=json.loads((root/'final/integer-candidate-ir.json').read_text())
cert=json.loads((root/'balanced/diagonal-certificate.json').read_text())
new=json.loads((root/'balanced/integer-ir.json').read_text())
poly=json.loads((root/'balanced/polynomial.json').read_text())
E=int(src['fixedParameter']['value'].split('^')[1])
p3={int(k):v for k,v in cert['threePowers'].items()}; p2={int(k):v for k,v in cert['twoPowers'].items()}
assert p3[0]==0 and p2[0]==0
div={r['id']:F(int(r['divisorNumerator']),int(r['divisorDenominator'])) for r in cert['rows']}
newrows={r['id']:r for r in new['residuals']}
quartic=defaultdict(int)
for r in src['residuals']:
    sub=defaultdict(F)
    for t in r['terms']:
        m=tuple(t['monomial'])
        sub[m]+=int(t['coefficient'])*F(3)**(E*t['sPower']+sum(p3[i] for i in m))*F(2)**sum(p2[i] for i in m)
    sub={m:a for m,a in sub.items() if a}
    d=div[r['id']]; assert d!=0
    got={tuple(t['monomial']):int(t['coefficient']) for t in newrows[r['id']]['terms']}
    assert {m:a/d for m,a in sub.items()}=={m:F(a) for m,a in got.items()}, r['name']
    for m,a in got.items():
        for n,b in got.items(): quartic[tuple(sorted(m+n))]+=a*b
compact={c['sourceId']:c['id'] for c in poly['coordinates']}
table={tuple(sorted(t['monomial'])):int(t['coefficient']) for t in poly['terms']}
assert table=={tuple(sorted(compact[i] for i in m)):a for m,a in quartic.items() if a}
print(json.dumps({'status':'PASS','rows':len(src['residuals']),'monomials':len(table),'maxDigits':max(len(str(abs(a))) for a in table.values()),'content':math.gcd(*table.values()),'x0^4':table.get((0,0,0,0))}))
