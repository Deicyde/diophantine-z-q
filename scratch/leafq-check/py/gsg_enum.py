# GammaStarGen: enumerate E+ = {v in O pure, nrd v = 1, <v,y> > 0}, y = i+j; B = (2,-3): i^2=2, j^2=-3, k=ij, k^2=6
from fractions import Fraction as Fr
import itertools, math
def mul(x,y):
    a1,b1,c1,d1=x; a2,b2,c2,d2=y
    # i^2=2, j^2=-3, k^2=6, ij=k, ji=-k, ik=i*ij=2j, ki=ij*i=-i*i*j... compute via rules
    # use generic quaternion algebra (a,b): i^2=a, j^2=b, k^2=-ab, ij=k=-ji, ik=a j, ki=-a j, jk=-b i, kj=b i
    A,Bq=2,-3
    return (a1*a2 + A*b1*b2 + Bq*c1*c2 - A*Bq*d1*d2,
            a1*b2 + b1*a2 - Bq*c1*d2 + Bq*d1*c2,
            a1*c2 + c1*a2 + A*b1*d2 - A*d1*b2,
            a1*d2 + d1*a2 + b1*c2 - c1*b2)
def conj(x): return (x[0],-x[1],-x[2],-x[3])
def nrd(x): return x[0]**2-2*x[1]**2+3*x[2]**2-6*x[3]**2
def inv(x):
    n=nrd(x); c=conj(x); return tuple(Fr(t)/n for t in c)
def form(v,w): return -2*v[1]*w[1]+3*v[2]*w[2]-6*v[3]*w[3]
def inO(x):
    # O = Z<1,i,(1+j)/2,(i+k)/2>: x=n0+n1 i+n2(1+j)/2+n3(i+k)/2 => d=n3/2, c=n2/2, b=n1+n3/2, a=n0+n2/2
    a,b,c,d=map(Fr,x)
    n3=2*d; n2=2*c; n1=b-n3/2; n0=a-n2/2
    return all(t.denominator==1 for t in (n0,n1,n2,n3))
y=(0,1,1,0)
assert nrd(y)==1
x4=(1,1,1,0); x6=(Fr(-3,2),0,Fr(1,2),0)
def E(bound):
    out=[]
    for c in range(-bound*2,bound*2+1):
        for B2 in range(-bound*4,bound*4+1):
            for D2 in range(-bound*4,bound*4+1):
                if (B2-D2)%2: continue
                if -B2*B2+6*c*c-3*D2*D2!=2: continue
                v=(0,Fr(B2,2),Fr(c),Fr(D2,2))
                ip=form(v,y)
                if 0<ip<=bound: out.append((ip,v))
    return sorted(out)
if __name__=="__main__":
    pts=E(12)
    print(len(pts))
    from collections import Counter
    print(Counter(p[0] for p in pts))
    for ip,v in pts[:20]: print(ip,v)
