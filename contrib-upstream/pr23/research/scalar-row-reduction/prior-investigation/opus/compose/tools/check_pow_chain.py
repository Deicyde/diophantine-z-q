"""Independent check (reads only the raw IR) that, in every detector, the weight gates
define q1^6, q1^12, q12=q1^23, mixedHigh=q1^46, q_k=q1^(2k-1), and the q_k powers 2,3,
and that the high-order evaluation and mixed block consume exactly these coordinates."""
import json, sys
from fractions import Fraction
ir = json.load(open(sys.argv[1])); k = int(sys.argv[2])
name = {c['id']: c['name'] for c in ir['coordinates']}
byname = {c['name']: c['id'] for c in ir['coordinates']}
gates = {g['coordinateId']: g for g in ir['gates']}
def mono(terms):
    assert len(terms) == 1, terms
    t = terms[0]; assert t['sPower'] == 0
    return Fraction(t['coefficient']), t['monomial']
ok = True
for r in range(3):
    exp = {byname[f'detector{r}.q1']: 1}
    # q1^2 and q1^3 aliases
    def resolve(cid):
        return exp[cid]
    def gate_exp(cid):
        g = gates[cid]
        if g['operation'] == 'quadratic_assignment':
            c, m = mono(g['expression']); assert c == 1
            return sum(resolve(x) for x in m)
        c, m = mono(g['numerator']); assert c == 1
        cd, md = mono(g['denominator']); assert cd == 1 and len(md) == 1
        return sum(resolve(x) for x in m) - resolve(md[0])
    order = ['q1SquaredForWeights.quadratic', 'q1CubedForWeights.quadratic', 'q1Sixth.quadratic', 'q1Twelfth.quadratic',
             'q12', 'mixedHigh.quadratic', f'q{k}', f'E{k}.power2.quadratic', f'E{k}.power3.quadratic']
    want = [2, 3, 6, 12, 23, 46, 2*k-1, 2*(2*k-1), 3*(2*k-1)]
    for n, w in zip(order, want):
        cid = byname[f'detector{r}.{n}']
        e = gate_exp(cid); exp[cid] = e
        print(r, n, 'q1^%d' % e, 'OK' if e == w else 'FAIL'); ok &= (e == w)
    # no e-chain remnants
    assert not any(n.startswith(f'detector{r}.e') and ('Cubed' in n or 'Sixth' in n or 'Twelfth' in n) for n in byname)
print('ALL_OK' if ok else 'FAIL')
