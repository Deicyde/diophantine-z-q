"""Pure-python reduction of polynomial identities in Q[s, I, t] modulo s^2-2 and I^2+1.
Used to produce linear_combination coefficients for Omega(sqrt2 + i) (part_nonzero.lean).
Polynomials: dict {(es, ei): Fraction}."""
from fractions import Fraction as Fr
from collections import defaultdict
def add(p,q,c=1):
    r=defaultdict(Fr); 
    for k,v in p.items(): r[k]+=v
    for k,v in q.items(): r[k]+=c*v
    return {k:v for k,v in r.items() if v!=0}
def mul(p,q):
    r=defaultdict(Fr)
    for k1,v1 in p.items():
        for k2,v2 in q.items(): r[(k1[0]+k2[0],k1[1]+k2[1])]+=v1*v2
    return {k:v for k,v in r.items() if v!=0}
def const(c): return {(0,0):Fr(c)} if c else {}
S={(1,0):Fr(1)}; I={(0,1):Fr(1)}
def reduce(p):
    """return (q1,q2,r) with p = q1*(s^2-2) + q2*(I^2+1) + r, r reduced"""
    q1={};q2={};p=dict(p)
    while True:
        k=next((k for k in p if k[0]>=2),None)
        if k is not None:
            c=p[k]; m={(k[0]-2,k[1]):c}; q1=add(q1,m); p=add(p,mul(m,add({(2,0):Fr(1)},const(-2))),-1); continue
        k=next((k for k in p if k[1]>=2),None)
        if k is not None:
            c=p[k]; m={(k[0],k[1]-2):c}; q2=add(q2,m); p=add(p,mul(m,add({(0,2):Fr(1)},const(1))),-1); continue
        return q1,q2,p
def show(p):
    if not p: return "0"
    terms=[]
    for (a,b),v in sorted(p.items()):
        mon="*".join(["(√2:ℂ)"]*a+["I"]*b) or "1"
        terms.append(f"({v})*{mon}")
    return " + ".join(terms)
def pw(p,n):
    r=const(1)
    for _ in range(n): r=mul(r,p)
    return r
tau=add(S,I)
t2=pw(tau,2)
half=Fr(1,2)
def sc(p,c): return {k:v*c for k,v in p.items()}
# Nf entries
Nf00=add(mul(S,add(add(sc(t2,half),tau),const(Fr(-3,2)))), add(sc(t2,-half),const(Fr(-3,2))))
Nf01=add(mul(S,add(add(sc(t2,-half),sc(tau,-1)),const(Fr(3,2)))), add(t2,const(3)))
Nf11=add(mul(S,add(add(t2,sc(tau,2)),const(-3))), add(sc(t2,-1),const(-3)))
dF=sc(mul(mul(S,add(tau,const(-3))),add(tau,const(1))),-half)
Om={ '00':add(sc(I,half),const(-half)), '01':const(1), '11':add(I,const(-1))}
for name,N in [('00',Nf00),('01',Nf01),('11',Nf11)]:
    diff=add(N,mul(Om[name],dF),-1)
    q1,q2,r=reduce(diff)
    print(name,"remainder:",show(r))
    print("  q_s:",show(q1)); print("  q_I:",show(q2))
