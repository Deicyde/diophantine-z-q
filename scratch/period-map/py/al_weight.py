"""fibre-qm-period: numerical support for QMDenZeroCM3 (zeros of S = sum_{m even} theta_m^8 on Omega(H)).
Checks (own computation; Omega(tau) re-implemented from pkg-I1's definitions as in g0-thetapoint):
 (1) automorphy weight of S∘Omega and P = prod_{m even} theta_m^2 ∘ Omega under elements of Gamma*;
 (2) vanishing orders of S and P at the CM points of discriminants -4, -3, -24.
Run: ~/pyenv/bin/python -I psi4_zeros.py"""
import sympy as sp, mpmath as mp
mp.mp.dps = 40
R = sp.Rational; s2 = sp.sqrt(2)
basis = [(1,0,0,0), (0,1,0,0), (R(1,2),0,R(1,2),0), (0,R(1,2),0,R(1,2))]
def iota(x):
    x0,x1,x2,x3 = [sp.nsimplify(t) for t in x]
    Mi = sp.Matrix([[s2,0],[0,-s2]]); Mj = sp.Matrix([[0,-3],[1,0]])
    return x0*sp.eye(2) + x1*Mi + x2*Mj + x3*Mi*Mj
tau = sp.symbols('tau'); v = sp.Matrix([tau, 1])
cols = [iota(b)*v for b in basis]
Pinv = sp.Matrix([[-1,1],[1,-2]]).inv()
E1 = sp.Matrix.hstack(cols[0], cols[1]); F1 = sp.Matrix.hstack(cols[2], cols[3]) * Pinv
Omf = sp.lambdify(tau, F1.inv()*E1, 'mpmath')
def theta(ch, Om, N=12):
    (a1,a2),(b1,b2) = ch
    s = mp.mpc(0)
    for n1 in range(-N, N+1):
        for n2 in range(-N, N+1):
            x1 = n1 + mp.mpf(a1)/2; x2 = n2 + mp.mpf(a2)/2
            Q = x1*x1*Om[0,0] + 2*x1*x2*Om[0,1] + x2*x2*Om[1,1]
            s += mp.exp(1j*mp.pi*(Q + x1*b1 + x2*b2))
    return s
chars = [((a1,a2),(b1,b2)) for a1 in (0,1) for a2 in (0,1) for b1 in (0,1) for b2 in (0,1)]
ev = [ch for ch in chars if (ch[0][0]*ch[1][0] + ch[0][1]*ch[1][1]) % 2 == 0]
def SP(t):
    Om = Omf(t); th = [theta(ch, Om) for ch in ev]
    return mp.fsum([x**8 for x in th]), mp.fprod([x**2 for x in th])
def mob(x):
    g = iota(x); return [mp.mpf(sp.N(g[r,s], 60)) for r,s in ((0,0),(0,1),(1,0),(1,1))]
def fixpt(x):
    a,b,c,d = mob(x); disc = (d-a)**2 + 4*b*c
    z = (-(d-a) + mp.sqrt(disc))/(2*c)
    return z if mp.im(z) > 0 else (-(d-a) - mp.sqrt(disc))/(2*c)
# --- period-map: weight of S*dF^4 under Atkin-Lehner elements of Gamma* (det != 1)
def qmul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y   # i^2=2, j^2=-3, k=ij, k^2 = -i^2 j^2 = 6
    return (a1*a2 + 2*b1*b2 - 3*c1*c2 + 6*d1*d2,
            a1*b2 + b1*a2 + 3*(c1*d2 - d1*c2),
            a1*c2 + c1*a2 + 2*(b1*d2 - d1*b2),
            a1*d2 + d1*a2 + b1*c2 - c1*b2)
def nrd(x): a,b,c,d = x; return a*a - 2*b*b + 3*c*c - 6*d*d
def conj(x): a,b,c,d = x; return (a,-b,-c,-d)
Bm = sp.Matrix([[sp.nsimplify(t) for t in b] for b in basis]).T
def inO(x):
    n = Bm.solve(sp.Matrix([sp.nsimplify(t) for t in x])); return all(t.is_integer for t in n)
def normalizes(x):
    N = nrd(x); xi = tuple(sp.nsimplify(t)/N for t in conj(x))
    return all(inO(qmul(qmul(x, b), xi)) and inO(qmul(qmul(xi, b), x)) for b in basis)
print("check iota multiplicative on basis:", all(sp.simplify(iota(qmul(a,b)) - iota(a)*iota(b)) == sp.zeros(2) for a in basis for b in basis))
dF = lambda t: (t-3)*(t+1)
for name, x in {"j (nrd 3)": (0,0,1,0), "mu=2j+ij (nrd 6)": (0,0,2,1), "2+i (nrd 2)": (2,1,0,0), "1+j": (1,0,1,0)}.items():
    x = tuple(sp.nsimplify(t) for t in x)
    print(name, "nrd", nrd(x), "normalizes O:", normalizes(x))
    if nrd(x) > 0 and normalizes(x):
        a,b,c,d = mob(x); det = a*d-b*c
        for t in [mp.mpc('0.3','1.1'), mp.mpc('-0.7','0.9')]:
            gt = (a*t+b)/(c*t+d); S1,P1 = SP(t); S2,P2 = SP(gt)
            r = abs(dF(gt)/dF(t))
            print(f"   t={mp.nstr(t,4)} det={mp.nstr(det,6)}: |S dF^-4 (gt)| / (|ct+d|^8 det^-4 |S dF^-4 (t)|) = {mp.nstr(abs(S2/S1)/r**4/abs(c*t+d)**8*det**4,12)}")
# --- second CM3 point tau3' = iota(2+i) . i sqrt3 and x' = u x u^{-1}
u = (2,1,0,0); x = (R(1,2),0,R(1,2),0); ui = tuple(sp.nsimplify(t)/nrd(u) for t in conj(u))
xp = qmul(qmul(u,x),ui); print("x' =", xp, "inO:", inO(xp), "x'^2-x'+1 =", tuple(sp.simplify(a-b+(1 if i==0 else 0)) for i,(a,b) in enumerate(zip(qmul(xp,xp),xp))))
Bm2 = Bm.solve(sp.Matrix(xp)); print("coords of x' in oBasis:", list(Bm2))
print("iota(x') =", iota(xp))
t3p = (3+2*mp.sqrt(2))*mp.sqrt(3)*1j
a,b,c,d = mob(xp); print("fixed point check:", mp.nstr((a*t3p+b)/(c*t3p+d) - t3p, 5))
S0,P0 = SP(t3p); e1, e2 = mp.mpf('1e-3'), mp.mpf('1e-4')
Sa,Pa = SP(t3p+e1*mp.mpc(1,0.37)); Sb,Pb = SP(t3p+e2*mp.mpc(1,0.37))
print("tau3': |S|=", mp.nstr(abs(S0),5), "ord S ~", mp.nstr(mp.log(abs(Sa)/abs(Sb))/mp.log(10),6))
t4 = mp.sqrt(2)+1j; S4,P4 = SP(t4); print("S(Omega(sqrt2+i)) =", mp.nstr(S4,12))
