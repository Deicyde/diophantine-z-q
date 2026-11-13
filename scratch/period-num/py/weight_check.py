"""period-num: checks behind part_weight.lean (S8WeightExact), pure python3.
B = (2,-3): i^2 = 2, j^2 = -3, k = ij.  O = Z<1, i, (1+j)/2, (i+ij)/2>.  Symplectic basis sB of O:
  e0 = 1, e1 = i, f0 = -2 b2 - b3, f1 = -b2 - b3  (b2 = (1+j)/2, b3 = (i+ij)/2; i.e. (b2,b3) Pinv).
For x = r w u (w in {1, i, j+ij, mu}, u a unit) with z = r^-1 w^-1: N[l][k] = kappa_l(z sB_k x) is integral,
N^T G N = G (G = gram in sB = [[0,I],[-I,0]]), Omega(g tau) = spAct(N^T, Omega(tau)), and
spFactor = j^2 det(iota z) dF(g tau)/dF(tau)."""
from fractions import Fraction as Fr
import cmath, math
def qmul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    return (a1*a2 + 2*b1*b2 - 3*c1*c2 + 6*d1*d2, a1*b2 + b1*a2 + 3*(c1*d2 - d1*c2),
            a1*c2 + c1*a2 + 2*(b1*d2 - d1*b2), a1*d2 + d1*a2 + b1*c2 - c1*b2)
def nrd(x): a,b,c,d = x; return a*a - 2*b*b + 3*c*c - 6*d*d
def conj(x): a,b,c,d = x; return (a,-b,-c,-d)
def sc(r,x): return tuple(r*t for t in x)
def inv(x): n=nrd(x); return tuple(Fr(t)/n for t in conj(x))
def trd(x): return 2*x[0]
H=Fr(1,2)
oB=[(1,0,0,0),(0,1,0,0),(H,0,H,0),(0,H,0,H)]
sB=[(1,0,0,0),(0,1,0,0),(-1,-H,-1,-H),(-H,-H,-H,-H)]
def kappa(a): a0,a1,a2,a3=a; return [a0-a2, a1-a3, 2*a3-2*a2, 2*a2-4*a3]
for k,s in enumerate(sB): assert kappa(s)==[1 if l==k else 0 for l in range(4)]
mu=(0,0,2,1); muInv=(0,0,Fr(-1,3),Fr(-1,6))
def Bf(a,b): return trd(qmul(qmul(muInv,a),conj(b)))
G=[[Bf(a,b) for b in sB] for a in sB]; print("G =",G)
s2=math.sqrt(2)
def iota(x):
    a,b,c,d=[float(t) for t in x]
    return [[a+b*s2, -3*c-3*s2*d],[c-s2*d, a-b*s2]]
def Omega(t):
    a=(t-3)/2; b=(t+1)/2
    F=[[-(2+s2)*a, -(1+s2)*a],[-(2-s2)*b, -(1-s2)*b]]
    E=[[t, s2*t],[1, -s2]]
    d=F[0][0]*F[1][1]-F[0][1]*F[1][0]
    Fi=[[F[1][1]/d, -F[0][1]/d],[-F[1][0]/d, F[0][0]/d]]
    return [[sum(Fi[i][k]*E[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def mm(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def madd(A,B): return [[A[i][j]+B[i][j] for j in range(len(A[0]))] for i in range(len(A))]
def minv2(A):
    d=A[0][0]*A[1][1]-A[0][1]*A[1][0]; return [[A[1][1]/d,-A[0][1]/d],[-A[1][0]/d,A[0][0]/d]]
def det2(A): return A[0][0]*A[1][1]-A[0][1]*A[1][0]
def dF(t): return -s2*(t-3)*(t+1)/2
W={"1":(1,0,0,0),"i":(0,1,0,0),"j+ij":(0,0,1,1),"mu":mu}
units=[(1,0,0,0),(1,1,0,0),(Fr(1,2),Fr(1,2),Fr(1,2),Fr(1,2))]  # sample units: 1, 1+i (nrd -1), ...
# find a few units in O by search (nrd +-1)
import itertools
U=[]
for n in itertools.product(range(-2,3),repeat=4):
    u=tuple(sum(Fr(n[k])*oB[k][c] for k in range(4)) for c in range(4))
    if abs(nrd(u))==1: U.append(u)
print("units found:",len(U))
def inO(a):
    a0,a1,a2,a3=a; n=[a0-a2, a1-a3, 2*a2, 2*a3]; return all(Fr(t).denominator==1 for t in n)
for name,w in W.items():
    winv=inv(w)
    norm_ok=all(inO(qmul(qmul(winv,b),w)) and inO(qmul(qmul(w,b),winv)) for b in oB)
    cw=Fr(Bf(qmul(qmul(winv,(1,0,0,0)),w),qmul(qmul(winv,sB[2]),w)),Bf((1,0,0,0),sB[2]))
    print(f"w={name}: nrd={nrd(w)} winv={winv} normalizes O: {norm_ok}; Bf(w^-1 a w, w^-1 b w)/Bf(a,b) = {cw}")
    # integer matrix of b -> winv b w in oBasis coordinates
    M=[[None]*4 for _ in range(4)]
    for k,b in enumerate(oB):
        c=qmul(qmul(winv,b),w); a0,a1,a2,a3=c; n=[a0-a2,a1-a3,2*a2,2*a3]
        for l in range(4): M[l][k]=n[l]
    print("   oBasis-coords of winv*oBasis_k*w (columns k):",[[str(t) for t in row] for row in M])
cnt=0
for name,w in W.items():
    for u in U[:12]:
        r=Fr(3,2)
        x=sc(r,qmul(w,u)); z=sc(1/r,inv(w))
        if nrd(x)<=0: continue
        N=[[kappa(qmul(qmul(z,sB[k]),x))[l] for k in range(4)] for l in range(4)]
        assert all(Fr(t).denominator==1 for row in N for t in row)
        NT=[[N[k][l] for k in range(4)] for l in range(4)]
        assert mm(mm(NT,G),N)==G, (name,u)
        g=iota(x)
        for t in [0.3+1.1j, -0.7+0.9j]:
            j=g[1][0]*t+g[1][1]; gt=(g[0][0]*t+g[0][1])/j
            Om=Omega(t); Omg=Omega(gt)
            Mf=[[float(v) for v in row] for row in NT]
            A=[r_[:2] for r_ in Mf[:2]]; Bm=[r_[2:] for r_ in Mf[:2]]; C=[r_[:2] for r_ in Mf[2:]]; D=[r_[2:] for r_ in Mf[2:]]
            CD=madd(mm(C,Om),D)
            act=mm(madd(mm(A,Om),Bm),minv2(CD))
            err=max(abs(act[a][b]-Omg[a][b]) for a in range(2) for b in range(2))
            fac=det2(CD); pred=j*j*det2(iota(z))*dF(gt)/dF(t)
            cnt+=1
            if cnt<=12 or err>1e-9 or abs(fac-pred)>1e-9:
                print(f"w={name} u={tuple(str(v) for v in u)} nrd(u)={nrd(u)} t={t}: |spAct-Omega(gt)|={err:.2e} |spFactor-pred|={abs(fac-pred):.2e}")
print("checked",cnt,"cases")
