# C4: bounded multipliers m = m0 k^2 (k <= 2^8) on 30 toy test-site inputs B = R0 (u/w)^2,
# R0 = 2730^6 |F(n)|, 0 < B < 1/2, w coprime to 2730 (square denominator, S0 valuations hold).
# (classes used unreduced: theta ~ m0(m0k^2w^2-R0u^2), beta ~ m0R0; points are equivalent.)
# For each (m0,k): theta = sqf(m0(m0k^2-B)), beta = sqf(m0 B).
#  (i) theta == 1 ?   (ii) one-curve shortcut: w^2 = theta(beta^2 s^4 - 1) has a point, height <= H
import random, time, cypari2
from fractions import Fraction as F
pari=cypari2.Pari(); pari.allocatemem(2*10**9)
random.seed(11)
C=[0,-15,-20,-24,-30,-60]
def core(x):
    x=F(x); n=x.numerator*x.denominator
    return int(pari.core(n))
H=20; M0=[1,2,3,5,6,7,10,13]
t0=time.time(); stats=[]
for i in range(30):
    n=random.randint(-10**3,10**3)
    while n in C: n+=1
    Fn=1
    for c in C: Fn*=(n-c)
    R0=2730**6*abs(Fn)
    while True:
        u=random.randint(1,10**3); w=pari.sqrtint(2*R0*u*u)+random.randint(1,10**6); w=int(w)
        if pari.gcd(w,2730)==1 and F(R0*u*u,w*w)<F(1,2): break
    B=F(R0*u*u,w*w)
    th1=0; one=0; onek=[]
    for m0 in M0:
        beta=m0*R0   # same class as sqf(m0 B); s rescales
        for k in range(1,257):
            m=m0*k*k
            if m==B: continue
            th=m0*(m*w*w-R0*u*u)   # same class as theta; no factoring needed
            if th>0 and pari.issquare(th): th1+=1; continue
            if th<0 and False: pass
            pol=pari(f"{th*beta*beta}*x^4-({th})")
            pts=pari.hyperellratpoints(pol,H)
            if len(pts)>0: one+=1; onek.append((m0,k))
    stats.append((n,th1,one,onek[:3]))
    print(i,"n=",n,"theta=1:",th1,"one-curve hits (height<=%d):"%H,one,"of",len(M0)*256,onek[:3],"t=%.0fs"%(time.time()-t0),flush=True)
tot=sum(s[2] for s in stats); cov=sum(1 for s in stats if s[2]>0)
print("TOTAL hits",tot,"of",30*len(M0)*256,"; inputs with at least one hit:",cov,"/30")
# sanity: theta := beta^2 s0^4 - 1 (s0 = 3/2) must be found by the same search
beta=7*10**20+3; th=(beta**2*81-16)*16
print("sanity hit:",len(pari.hyperellratpoints(pari(f"{th*beta*beta}*x^4-({th})"),H))>0)
