"""rv-leaves-a: independent numerical check of PkgI1.QMHauptmodul, coded from the Lean definitions
(iota, latVec, Emat, F0mat, Pinv, Omega, thetaConst, evenChars, jNum, jDen) only.
Checks: Omega(tau) in Siegel H2; Gamma*-invariance under Atkin-Lehner elements of norms 2,3,6 found
by search in O; values and local orders at the fixed points of x in O with x^2=-1, x^2-x+1=0, x^2=-6."""
import mpmath as mp, itertools
mp.mp.dps = 30
s2 = mp.sqrt(2)
def qmul(x, y):
    a, c = 2, -3
    x0,x1,x2,x3 = x; y0,y1,y2,y3 = y
    return (x0*y0 + a*x1*y1 + c*x2*y2 - a*c*x3*y3, x0*y1 + x1*y0 - c*x2*y3 + c*x3*y2,
            x0*y2 + x2*y0 + a*x1*y3 - a*x3*y1, x0*y3 + x3*y0 + x1*y2 - x2*y1)
from fractions import Fraction as Fr
basis = [(1,0,0,0),(0,1,0,0),(Fr(1,2),0,Fr(1,2),0),(0,Fr(1,2),0,Fr(1,2))]
def fromO(n): return tuple(sum(Fr(n[k])*basis[k][t] for k in range(4)) for t in range(4))
def inO(x):  # coordinates: x = n0 + n1 i + n2 (1+j)/2 + n3 (i+ij)/2
    n2 = 2*x[2]; n3 = 2*x[3]; n0 = x[0]-n2/2; n1 = x[1]-n3/2
    return all(Fr(t).denominator == 1 for t in (n0,n1,n2,n3))
def nrd(x): return x[0]**2 - 2*x[1]**2 + 3*x[2]**2 - 6*x[3]**2
def conj(x): return (x[0],-x[1],-x[2],-x[3])
def normalizes(x):
    N = nrd(x); xi = tuple(Fr(t)/N for t in conj(x))
    return all(inO(qmul(qmul(x,b),xi)) and inO(qmul(qmul(xi,b),x)) for b in basis)
Mi = mp.matrix([[s2,0],[0,-s2]]); Mj = mp.matrix([[0,-3],[1,0]])
def iota(x): return float(x[0])*mp.eye(2) + mp.mpf(x[1].numerator)/x[1].denominator*Mi if False else \
    mp.mpf(Fr(x[0]).numerator)/Fr(x[0]).denominator*mp.eye(2) + mp.mpf(Fr(x[1]).numerator)/Fr(x[1]).denominator*Mi \
    + mp.mpf(Fr(x[2]).numerator)/Fr(x[2]).denominator*Mj + mp.mpf(Fr(x[3]).numerator)/Fr(x[3]).denominator*(Mi*Mj)
def Omega(t):
    v = mp.matrix([t,1]); cols = [iota(b)*v for b in basis]
    E = mp.matrix([[cols[0][0],cols[1][0]],[cols[0][1],cols[1][1]]])
    F0 = mp.matrix([[cols[2][0],cols[3][0]],[cols[2][1],cols[3][1]]])
    Pinv = mp.matrix([[-2,-1],[-1,-1]])
    return (F0*Pinv)**-1 * E
chars = [((a0,a1),(b0,b1)) for a0,a1,b0,b1 in itertools.product((0,1),repeat=4) if (a0*b0+a1*b1)%2==0]
assert len(chars) == 10
def theta(ch, Om, N=12):
    (a0,a1),(b0,b1) = ch; s = 0
    for n0 in range(-N,N+1):
        for n1 in range(-N,N+1):
            v0 = n0+a0/2; v1 = n1+a1/2
            q = v0*(Om[0,0]*v0+Om[0,1]*v1) + v1*(Om[1,0]*v0+Om[1,1]*v1)
            s += mp.exp(mp.pi*1j*q + mp.pi*1j*(v0*b0+v1*b1))
    return s
def jparts(t):
    Om = Omega(t); th = [theta(c,Om) for c in chars]
    S8 = sum(x**8 for x in th); P2 = mp.fprod([x**2 for x in th])
    return 3779136*P2**2, S8**5
def jth(t):
    n, d = jparts(t); return n/d
def moeb(g, t): return (g[0,0]*t+g[0,1])/(g[1,0]*t+g[1,1])
def fixpt(x):
    g = iota(x); a,b,c,d = g[0,0],g[0,1],g[1,0],g[1,1]
    r = mp.polyroots([c, d-a, -b])
    return [z for z in r if mp.im(z) > 0][0]
out = []
# 1. Omega in H2 at sample points
for t in [0.3+1.1j, -0.7+0.6j, 1.9+2.0j]:
    Om = Omega(mp.mpc(t)); sym = abs(Om[0,1]-Om[1,0])
    Y = [[mp.im(Om[i,j]) for j in range(2)] for i in range(2)]
    out.append(f"Omega({t}): |asym|={mp.nstr(sym,3)} ImOm00={mp.nstr(Y[0][0],6)} detIm={mp.nstr(Y[0][0]*Y[1][1]-Y[0][1]*Y[1][0],6)}")
# 2. Atkin-Lehner elements by search
found = {}
rng = range(-2,3)
for n in itertools.product(rng, repeat=4):
    x = fromO(n); N = nrd(x)
    if N in (2,3,6) and N not in found and normalizes(x): found[N] = x
out.append(f"normalizer elements found (nrd: x): {found}")
t0 = mp.mpc(0.31, 0.83)
j0 = jth(t0)
for N, x in sorted(found.items()):
    j1 = jth(moeb(iota(x), t0))
    out.append(f"invariance nrd {N}: |j(gt)-j(t)|/|j(t)| = {mp.nstr(abs(j1-j0)/abs(j0),3)}")
# 3. CM points and local orders
cm = {"-4 (x=i+j, x^2=-1)": ((0,1,1,0), 0), "-3 (x=(1+j)/2)": ((Fr(1,2),0,Fr(1,2),0), None),
      "-24 (x=mu=2j+ij)": ((0,0,2,1), mp.mpf(-16)/27)}
for name, (x, val) in cm.items():
    tz = fixpt(x)
    vals = []
    for eps in (mp.mpf('1e-2'), mp.mpf('1e-3')):
        n, d = jparts(tz + eps*mp.mpc(0.6,0.8))
        vals.append((n, d))
    if val is None:
        r = [abs(d/n) for n,d in vals]   # 1/j
    else:
        r = [abs(n/d - val) for n,d in vals]
    order = mp.log(r[0]/r[1])/mp.log(10)
    n, d = jparts(tz)
    out.append(f"CM {name}: tau={mp.nstr(tz,10)} |jNum|={mp.nstr(abs(n),5)} |jDen|={mp.nstr(abs(d),5)} "
               f"j={mp.nstr(n/d,12) if abs(d)>1e-20 else 'pole'}  local order in tau ~ {mp.nstr(order,4)}")
# 4. an extra x^2 = -1 element (different optimal embedding) gives the same value
for n in itertools.product(range(-3,4), repeat=4):
    x = fromO(n)
    if x != (0,1,1,0) and x[0] == 0 and nrd(x) == 1 and x[1] != 0 and x[3] != 0:
        tz = fixpt(x); out.append(f"x={x} (x^2=-1): j at fixed point = {mp.nstr(jth(tz),8)}"); break
for n in itertools.product(range(-3,4), repeat=4):
    x = fromO(n)
    if x != (0,0,2,1) and x[0] == 0 and nrd(x) == 6 and x[1] != 0:
        tz = fixpt(x); out.append(f"x={x} (x^2=-6): j at fixed point = {mp.nstr(jth(tz),8)}"); break
print("\n".join(out))
