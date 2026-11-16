# t21-proof: rational certificates for Re/Im of the main sum S = sum_j c_j (pi/M) mainL(j/M),
# c_j = (cr + ci i)/4; term (j,m,n): alpha = (j1 - M m, j2 - M n), N = |alpha|^2,
# Re = (cr a1 - ci a2)/(4N) E^N, Im = (ci a1 + cr a2)/(4N) E^N, E = exp(-pi/M^2) in [l,u].
from fractions import Fraction as Fr
def uRe(a,b):
    a%=4;b%=4
    return 1 if (a,b) in [(1,0),(3,2)] else (-1 if (a,b) in [(3,0),(1,2)] else 0)
def uIm(a,b):
    a%=4;b%=4
    return 1 if (a,b) in [(0,3),(2,1)] else (-1 if (a,b) in [(0,1),(2,3)] else 0)
def jac12(n):
    r=n%12
    return 1 if r in (1,11) else (-1 if r in (5,7) else 0)
def coeffs(d,j1,j2):
    if d==1: return uRe(j1,j2),uIm(j1,j2)
    J=jac12(j1*j1+j2*j2); return J*uRe(j1,j2),J*uIm(j1,j2)
def bounds(d,M,l,u):
    rl=rh=il=ih=Fr(0); W=0
    for j1 in range(M):
        for j2 in range(M):
            cr,ci=coeffs(d,j1,j2); W+=abs(cr)+abs(ci)
            for m in (0,1):
                for n in (0,1):
                    a1=j1-M*m;a2=j2-M*n;N=a1*a1+a2*a2
                    if N==0: continue
                    for q,lo_hi in ((Fr(cr*a1-ci*a2,4*N),'r'),(Fr(ci*a1+cr*a2,4*N),'i')):
                        lo = q*l**N if q>=0 else q*u**N
                        hi = q*u**N if q>=0 else q*l**N
                        if lo_hi=='r': rl+=lo; rh+=hi
                        else: il+=lo; ih+=hi
    return float(rl),float(rh),float(il),float(ih),W
import math
for d,M,l,u in [(1,4,Fr(8036,10000),Fr(836,1000)),(3,12,Fr(9781,10000),Fr(9787,10000))]:
    x=math.pi/M**2
    print(d,M,"l<=1-x",float(l)<=1-3.141593/M**2,"u>=1/(1+x)",float(u)>=1/(1+3.141592/M**2))
    rl,rh,il,ih,W=bounds(d,M,l,u)
    err=(15.2/20+0.2487)/(4*M)*W
    print(" Re",rl,rh," Im",il,ih," W",W," err",err," ReL>=",rl-err, " |L|<=",max(abs(rl),abs(rh))+max(abs(il),abs(ih))+err)
