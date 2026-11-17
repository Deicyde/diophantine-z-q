"""Independent check: in variant A, each changed row equals the old row plus a constant
combination of the two x(S) definition rows (an invertible row operation)."""
import json, sys
from fractions import Fraction as F
old=json.load(open(sys.argv[1])); new=json.load(open(sys.argv[2]))
assert old['coordinates']==new['coordinates'] and len(old['residuals'])==len(new['residuals'])
P=lambda r:{(int(t['sPower']),tuple(sorted(t['monomial']))):F(t['coefficient']) for t in r['terms']}
byname={r['name']:r for r in old['residuals']}
g0,g1=P(byname['S.chart.x.0.definition']),P(byname['S.chart.x.1.definition'])
x0=next(c['id'] for c in old['coordinates'] if c['name']=='S.chart.x.0.quadratic')
x1=next(c['id'] for c in old['coordinates'] if c['name']=='S.chart.x.1.quadratic')
changed=[]
for a,b in zip(old['residuals'],new['residuals']):
    assert a['name']==b['name'] and a['id']==b['id']
    pa,pb=P(a),P(b)
    if pa==pb: continue
    d={k:pb.get(k,0)-pa.get(k,0) for k in set(pa)|set(pb)}
    # gate rows are h-expr - x ; the coefficient of x in d determines lambda
    l0=-d.get((0,(x0,)),0)/g0[(0,(x0,))]*-1 if False else d.get((0,(x0,)),0)/g0[(0,(x0,))]
    l1=d.get((0,(x1,)),0)/g1[(0,(x1,))]
    comb={k:l0*g0.get(k,0)+l1*g1.get(k,0) for k in set(g0)|set(g1)}
    assert all(d.get(k,0)==comb.get(k,0) for k in set(d)|set(comb)), a['name']
    assert all(x0 not in k[1] or len(k[1])==2 for k in pb) and (0,(x0,)) not in pb and (0,(x1,)) not in pb
    changed.append((a['name'],str(l0),str(l1)))
print(json.dumps({'status':'PASS','changedRows':changed},indent=1))
