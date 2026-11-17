"""Evaluate the actual raw IR gates at random rational base values and check the semantic weights:
values[detector r.q47] = e^93/delta^3, q12 = e^23/delta, mixedHigh = q12^2, Rinv = 1/E, with
t = values[t], A = values[scale], e = (A*delta)^5/F(t). Also re-checks every row of the chain."""
import json, sys, random
from fractions import Fraction as Fr
from functools import lru_cache
d=json.load(open(sys.argv[1])); order=int(sys.argv[2]); bexp=int(sys.argv[3])
S=Fr(3)**int(d['fixedParameter']['value'].split('^')[1])
gates={g['coordinateId']:g for g in d['gates']}
random.seed(int(sys.argv[4]) if len(sys.argv)>4 else 1)
base={}
def poly(terms,val):
    s=Fr(0)
    for t in terms:
        v=Fr(t['coefficient'])*(S**t['sPower'] if t['sPower'] else 1)
        for i in t['monomial']: v*=val(i)
        s+=v
    return s
memo={}
def val(i):
    if i in memo: return memo[i]
    g=gates.get(i)
    if g is None: x=Fr(random.randint(1,60),random.randint(1,9))
    elif g['operation']=='quadratic_assignment': x=poly(g['expression'],val)
    elif g['operation']=='rational_quotient': x=poly(g['numerator'],val)/poly(g['denominator'],val)
    else: raise ValueError(g['operation'])
    memo[i]=x; return x
cs=[Fr(1)]
for root in [Fr(0),Fr(1,49),Fr(1,50),Fr(1,2450),Fr(32,1225)]:
    o=[Fr(0)]*(len(cs)+1)
    for j,c in enumerate(cs): o[j]-=root*c; o[j+1]+=c
    cs=o
V=lambda n: poly(d['values'][n]['terms'],val)
for r in range(3):
    p=f'detector{r}.'
    t=V(p+'t'); lam=val(next(c['id'] for c in d['coordinates'] if c['name']=='lambda')); A=t/lam; assert A==(1 if r==0 else V('heightProduct.scale%d'%(r-1))); delta=98*t-1; Fv=sum(c*t**j for j,c in enumerate(cs))
    assert V(p+'F')==Fv
    e=(A*delta)**5/Fv
    assert V(p+'q1')==e/delta and V(p+'eDelta')==e*delta
    assert V(p+'q12')==e**23/delta and V(p+'mixedHigh')==e**46/delta**2
    q=V(p+f'q{order}'); assert q==e**(2*order-1)*delta**bexp, p
    if p+'Rinv' in d['values']: assert V(p+'Rinv')*e*delta==1
    assert V(p+f'E{order}.power2')==q**2 and V(p+f'E{order}.power3')==q**3
    print(p,'A=',A,'semantic q%d = e^%d delta^%d ok'%(order,2*order-1,bexp))
# every residual row touching these coordinates must vanish at the gate-evaluated point
names={c['id']:c['name'] for c in d['coordinates']}
cnt=0
for row in d['residuals']:
    if row['block'].startswith('detector') and any(k in row['name'] for k in ['Rinv','qFive','qEleven','q12','mixedHigh',f'q{order}','eCubed','eSixth','eTwelfth']):
        assert poly(row['terms'],val)==0,row['name']; cnt+=1
print('rows checked',cnt)
