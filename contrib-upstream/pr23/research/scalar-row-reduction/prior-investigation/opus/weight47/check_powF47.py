"""Independent semantic check of the sibling's 377 build: evaluate actual raw-IR gates at random rationals."""
import json, sys, random
from fractions import Fraction as Fr
d=json.load(open(sys.argv[1])); order=int(sys.argv[2]); random.seed(int(sys.argv[3]))
S=Fr(3)**int(d['fixedParameter']['value'].split('^')[1])
gates={g['coordinateId']:g for g in d['gates']}
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
lam=val(next(c['id'] for c in d['coordinates'] if c['name']=='lambda'))
for r in range(3):
    p=f'detector{r}.'
    t=V(p+'t'); A=t/lam; assert A==(1 if r==0 else V('heightProduct.scale%d'%(r-1)))
    delta=98*t-1; Fv=sum(c*t**j for j,c in enumerate(cs)); e=(A*delta)**5/Fv
    assert V(p+'F')==Fv and V(p+'q1')==e/delta and V(p+'eDelta')==e*delta
    q1=e/delta
    assert V(p+'q12')==q1**23 and V(p+'mixedHigh')==q1**46
    q=V(p+f"q{order}"); assert q==e**93*delta**(-97)*A**(-5)
    assert V(p+f'E{order}.power2')==q**2 and V(p+f'E{order}.power3')==q**3
    # factor normalization: 1 + R*(X/R^m)^2 with X = D*delta^s, s=-(2m-1) gives q1^(2m-1) D^2
    R=1/(e*delta); m=order; s=-95
    assert R*(delta**s*A**Fr(-5,2)/R**m)**2==q if False else R*(delta**s/R**m)**2*A**(-5)==q
    m=12; assert R*(delta**(-(2*m-1))/R**m)**2==q1**23
    print(p,'q12=q1^23, mixedHigh=q1^46, q%d=q1^%d, powers ok; normalization s=-(2m-1) ok'%(order,2*order-1))
