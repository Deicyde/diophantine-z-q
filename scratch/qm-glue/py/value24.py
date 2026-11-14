# Independent numerical check (double precision, pure Python) of ThetaQuotientValue24 from the Lean
# definitions (HDec.PkgI1 in ZInQKernel/OneProof/H/LPrefix.lean): Omega(tau) = (F0 Pinv)^{-1} E,
# theta constants over Z^2, jNum = 3779136*prod2^2, jDen = sum8^5.
import cmath, math, itertools
s2 = math.sqrt(2)
def mm(A,B): return [[sum(A[r][k]*B[k][c] for k in range(2)) for c in range(2)] for r in range(2)]
def add(*Ms): return [[sum(M[r][c] for M in Ms) for c in range(2)] for r in range(2)]
def sc(a,M): return [[a*M[r][c] for c in range(2)] for r in range(2)]
def inv(M):
    d = M[0][0]*M[1][1]-M[0][1]*M[1][0]; return [[M[1][1]/d,-M[0][1]/d],[-M[1][0]/d,M[0][0]/d]]
Mi = [[s2,0],[0,-s2]]; Mj = [[0,-3],[1,0]]; One = [[1,0],[0,1]]
def iota(a,b,c,d): return add(sc(a,One),sc(b,Mi),sc(c,Mj),sc(d,mm(Mi,Mj)))
oB = [(1,0,0,0),(0,1,0,0),(.5,0,.5,0),(0,.5,0,.5)]
def latvec(x,tau):
    M = iota(*x); return [M[r][0]*tau + M[r][1] for r in range(2)]
def Omega(tau):
    E = [[latvec(oB[c],tau)[r] for c in range(2)] for r in range(2)]
    F0 = [[latvec(oB[2+c],tau)[r] for c in range(2)] for r in range(2)]
    return mm(inv(mm(F0,[[-2,-1],[-1,-1]])),E)
def theta(m, Om, N=10):
    (a0,a1),(b0,b1) = m; tot = 0j
    for n0 in range(-N,N+1):
        for n1 in range(-N,N+1):
            v = [n0+a0/2, n1+a1/2]
            q = sum(v[r]*Om[r][c]*v[c] for r in range(2) for c in range(2))
            tot += cmath.exp(math.pi*1j*q + math.pi*1j*(v[0]*b0+v[1]*b1))
    return tot
chars = [((a0,a1),(b0,b1)) for a0,a1,b0,b1 in itertools.product(range(2),repeat=4) if (a0*b0+a1*b1)%2==0]
def jtheta(tau):
    Om = Omega(tau); th = [theta(m,Om) for m in chars]
    s8 = sum(t**8 for t in th); p2 = 1
    for t in th: p2 *= t**2
    return 3779136*p2**2/s8**5, Om, th
tau = 1j*math.sqrt(9+6*s2)
M = iota(0,0,2,1); print("fixed-point residual", (M[0][0]*tau+M[0][1])/(M[1][0]*tau+M[1][1]) - tau)
j, Om, th = jtheta(tau)
print("j_theta(tau24) =", j, "  j + 16/27 =", j+16/27)
print("Omega =", Om)
print("|theta_m| =", [round(abs(t),10) for t in th])
for name,t in [("sqrt2+i (disc -4)", s2+1j), ("i sqrt3 (disc -3)", 1j*math.sqrt(3))]:
    Om = Omega(t); th=[theta(m,Om) for m in chars]; s8=sum(x**8 for x in th); p2=1
    for x in th: p2*=x**2
    print(name, "jNum =", abs(3779136*p2**2), " jDen =", abs(s8**5))
