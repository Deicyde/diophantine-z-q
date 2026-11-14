# leaf-review-a: independent numeric check of PkgI1.Omega / QMHauptmodul / QMDenZeroCM3 (Leaves3.lean l.240-380)
import mpmath as mp
mp.mp.dps = 40
s2 = mp.sqrt(2)
Mi = mp.matrix([[s2,0],[0,-s2]]); Mj = mp.matrix([[0,-3],[1,0]]); I2 = mp.eye(2)
def iota(q):  # q=(re,i,j,k), B=(2,-3): i^2=2, j^2=-3, k=ij
    return q[0]*I2 + q[1]*Mi + q[2]*Mj + q[3]*(Mi*Mj)
oB = [(1,0,0,0),(0,1,0,0),(0.5,0,0.5,0),(0,0.5,0,0.5)]
def latvec(q,t): return iota(q)*mp.matrix([[t],[1]])
def Omega(t):
    E = mp.matrix(2,2); F0 = mp.matrix(2,2)
    for c in range(2):
        v = latvec(oB[c],t); w = latvec(oB[c+2],t)
        for r in range(2): E[r,c]=v[r]; F0[r,c]=w[r]
    Pinv = mp.matrix([[-2,-1],[-1,-1]])
    return mp.inverse(F0*Pinv)*E
chars=[((a0,a1),(b0,b1)) for a0 in (0,1) for a1 in (0,1) for b0 in (0,1) for b1 in (0,1)]
even=[m for m in chars if (m[0][0]*m[1][0]+m[0][1]*m[1][1])%2==0]
def theta(m,Om,N=12):
    s=0
    for n0 in range(-N,N+1):
        for n1 in range(-N,N+1):
            v=[n0+m[0][0]/2.0, n1+m[0][1]/2.0]
            q=sum(v[i]*Om[i,j]*v[j] for i in range(2) for j in range(2))
            s+=mp.exp(mp.pi*1j*q + mp.pi*1j*(v[0]*m[1][0]+v[1]*m[1][1]))
    return s
def jparts(t):
    Om=Omega(t); th=[theta(m,Om) for m in even]
    S=sum(x**8 for x in th); P=1
    for x in th: P*=x**2
    return S,P
def jth(t):
    S,P=jparts(t); return 3779136*P**2/S**5
for name,t in [("disc-4 sqrt2+i",s2+1j),("disc-24 i*sqrt(9+6sqrt2)",1j*mp.sqrt(9+6*s2))]:
    Om=Omega(t)
    print(name,"Omega sym err",mp.nstr(abs(Om[0,1]-Om[1,0]),5),"Im eig",[mp.nstr(e,6) for e in mp.eig(mp.matrix([[Om[i,j].imag for j in range(2)] for i in range(2)]))[0]])
    print("  j_theta =",mp.nstr(jth(t),15))
# order of vanishing of Sum theta^8 at i*sqrt3 (disc -3)
t0=1j*mp.sqrt(3)
for eps in [mp.mpf('1e-2'),mp.mpf('1e-3')]:
    S,P=jparts(t0+eps)
    print("eps",eps,"|S|",mp.nstr(abs(S),8),"|P|",mp.nstr(abs(P),8))
# Gamma*-invariance at one generic tau for gamma = iota(x), x in {j (norm 3), mu=2j+ij (norm 6), (1+j)/2 (norm 1)}
def mob(M,t): return (M[0,0]*t+M[0,1])/(M[1,0]*t+M[1,1])
t=mp.mpc(0.3,1.7); base=jth(t); print("generic j_theta",mp.nstr(base,15))
for nm,q in [("j",(0,0,1,0)),("mu",(0,0,2,1)),("(1+j)/2",(0.5,0,0.5,0))]:
    M=iota(q); print(nm,"det",mp.nstr(mp.det(M),6),"j_theta(g t)-j_theta(t)",mp.nstr(abs(jth(mob(M,t))-base),5))
# automorphy weight of Sum theta^8 o Omega under gamma=iota((1+j)/2) (det 1): ratio S(g t)/S(t)/(c t+d)^k for k=8
M=iota((0.5,0,0.5,0))
for t in [mp.mpc(0.3,1.7),mp.mpc(-1.1,0.8)]:
    S1,_=jparts(t); S2,_=jparts(mob(M,t)); f=M[1,0]*t+M[1,1]
    print("tau",t,"S(g t)/S(t)/(ct+d)^8 =",mp.nstr(S2/S1/f**8,12))
# honest automorphy: g = S(Omega(t)) * q(t)^a, q(t)=(t-3)(t+1) (det F0(t) = -sqrt2 q(t)/2, no zeros on H)
q=lambda t:(t-3)*(t+1)
for a in (4,-4):
  for k in (0,8):
    vals=[]
    for t in [mp.mpc(0.3,1.7),mp.mpc(-1.1,0.8)]:
        S1,_=jparts(t); S2,_=jparts(mob(M,t)); f=M[1,0]*t+M[1,1]
        vals.append(S2*q(mob(M,t))**a/(S1*q(t)**a*f**k))
    print("a",a,"k",k,[mp.nstr(v,10) for v in vals])
