# Brute-force explicit 2-Selmer system of E_l: y^2 = x(x-l)(x+3l), Kummer coords (x+3l, x-l),
# by local solubility searches at p | 6l and at infinity (good primes: unramified classes assumed,
# Silverman X.4), and comparison with the manuscript's matrix conditions (L1036-1074).
import sys, itertools
from fractions import Fraction as F
def vp(n,p):
    n=abs(n); c=0
    while n%p==0: n//=p; c+=1
    return c
def factor(n):
    fs=[];d=2
    while d*d<=n:
        while n%d==0: fs.append(d); n//=d
        d+=1
    if n>1: fs.append(n)
    return fs
def issq_p(q,p):
    if q==0: return True
    a,b=q.numerator,q.denominator
    v=vp(a,p)-vp(b,p)
    if v%2: return False
    u=F(a,p**vp(a,p))/F(b,p**vp(b,p))
    if p==2:
        return (u.numerator*u.denominator)%8==1
    return pow((u.numerator*u.denominator)%p,(p-1)//2,p)==1
def loc_p(l,a,b,p,K=5,M=None):
    if issq_p(F(a),p) and issq_p(F(b),p): return True
    if M is None: M = 7 if p==2 else (3 if p<50 else 2)
    for x in [F(0),F(l),F(-3*l)]:
        if issq_p((x+3*l)/a,p) and issq_p((x-l)/b,p) and issq_p(x/(a*b),p): return True
    for k in range(-K,K+1):
        for t in range(0,p**M):
            if t%p==0 and t!=0: continue
            x=F(t)*F(p)**k
            if issq_p((x+3*l)/a,p) and issq_p((x-l)/b,p) and issq_p(x/(a*b),p): return True
    return False
def loc_inf(l,a,b):
    if a>0 and b>0: return True
    for x in [F(-3*l),F(-2*l),F(-l),F(0),F(l),F(2*l),F(10*l)]:
        if (x+3*l)/a>=0 and (x-l)/b>=0 and x/(a*b)>=0: return True
    return False
def sqfree_divs(primes):
    out=[]
    for r in range(len(primes)+1):
        for c in itertools.combinations(primes,r):
            m=1
            for x in c: m*=x
            out+= [m,-m]
    return out
def selmer(l):
    ps=sorted(set([2,3]+factor(l)))
    cands=sqfree_divs(ps)
    S=[]
    for a in cands:
        if not loc_inf(l,a,1) and not any(loc_inf(l,a,b) for b in cands): continue
        for b in cands:
            if not loc_inf(l,a,b): continue
            if all(loc_p(l,a,b,p) for p in ps): S.append((a,b))
    return S
def leg(a,q):  # additive Legendre symbol
    a%=q
    return 0 if pow(a,(q-1)//2,q)==1 else 1
def matrix_conditions(l,beta):
    Q=sorted(factor(l)); n=len(Q)
    K=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i!=j:
                K[i][j]=leg(Q[j],Q[i]); K[i][i]^=leg(Q[j],Q[i])
    lam=[leg(3,q) for q in Q]
    # kernel by brute force
    ker=[]
    for v in itertools.product([0,1],repeat=n):
        if all(sum(K[i][j]*v[j] for j in range(n))%2==0 for i in range(n)): ker.append(v)
    one=tuple([1]*n); ob=tuple([1 if beta%q==0 else 0 for q in Q])
    span={tuple([0]*n),one,ob,tuple(x^y for x,y in zip(one,ob))}
    kerok = set(ker)==span and len(span)==4
    imK=set()
    for u in itertools.product([0,1],repeat=n):
        imK.add(tuple(sum(K[i][j]*u[j] for j in range(n))%2 for i in range(n)))
    lamok = tuple(lam) not in imK
    return kerok, lamok, len(ker)
if __name__=="__main__":
    import random
    lo,hi=int(sys.argv[1]),int(sys.argv[2])
    for l in range(lo,hi):
        if l%12!=11: continue
        fs=factor(l)
        if len(set(fs))!=len(fs): continue
        S=selmer(l)
        # beta candidates: divisors of l, = 17 mod 24, with (beta,1) in S
        betas=[a for (a,b) in S if b==1 and a>0 and a%24==17]
        mc=[(bt,matrix_conditions(l,bt)) for bt in set(d for d in sqfree_divs(fs) if d>0 and d%24==17)]
        print(l, fs, len(S), "beta-classes:",betas, "matrix:",mc)
