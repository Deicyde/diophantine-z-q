# t21-proof: the main sum Re sum_{j,m,n} c_j alpha/|alpha|^2 E^{|alpha|^2} with interval bounds on E.
import math
from fractions import Fraction as Fr
exec(open('scratch/t21-proof/lsplit.py').read().split('for (d,M,t)')[0])
def mainsum(d,M):
    x_lo=Fr(3141592,10**6)/M**2; x_hi=Fr(3141593,10**6)/M**2
    l=1-x_hi; u=1/(1+x_lo)
    exact=0; lo=0; hi=0; cnt=0
    for j1 in range(M):
        for j2 in range(M):
            c=twChar(d,M,j1,j2)
            if c==0: continue
            cr=round(4*c.real) if isinstance(c,complex) else round(4*c); ci=round(4*c.imag) if isinstance(c,complex) else 0
            for m in (0,1):
                for n in (0,1):
                    a1=j1-M*m; a2=j2-M*n; N=a1*a1+a2*a2
                    if N==0: continue
                    R=cr*a1-ci*a2
                    if R==0: continue
                    cnt+=1
                    q=Fr(R,4*N)
                    exact+=float(q)*math.exp(-math.pi*N/M**2)
                    if q>0: lo+=q*l**N; hi+=q*u**N
                    else: lo+=q*u**N; hi+=q*l**N
    return exact,float(lo),float(hi),cnt
for d,M in [(1,4),(3,12)]:
    print(d,M,mainsum(d,M))
def mainsum2(d,M,l,u):
    lo=0; hi=0
    for j1 in range(M):
        for j2 in range(M):
            c=twChar(d,M,j1,j2)
            if c==0: continue
            cr=round(4*complex(c).real); ci=round(4*complex(c).imag)
            for m in (0,1):
                for n in (0,1):
                    a1=j1-M*m; a2=j2-M*n; N=a1*a1+a2*a2
                    if N==0: continue
                    q=Fr(cr*a1-ci*a2,4*N)
                    if q>0: lo+=q*l**N; hi+=q*u**N
                    else: lo+=q*u**N; hi+=q*l**N
    return float(lo),float(hi)
print("C1 crude", mainsum2(1,4,Fr(2009,2500),Fr(836,1000)))
print("C3 crude", mainsum2(3,12,Fr(489,500),Fr(9787,10000)))
