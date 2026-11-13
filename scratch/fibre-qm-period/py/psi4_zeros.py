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
# (1) weights: gamma = iota(x) for x in O with nrd > 0
print("(1) automorphy: |S(g t)/S(t)| / |c t + d|^8 * |detF'(g t)/detF'(t)|^(+-4), same for P with 20, +-10 (1 = weight 8 / 20 form after the det F' normalization)")
gens = {"(1+j)/2": (R(1,2),0,R(1,2),0), "i+j": (0,1,1,0), "3+2i (nrd 1)": (3,2,0,0)}
for name, x in gens.items():
    a,b,c,d = mob(x); det = a*d-b*c
    for t in [mp.mpc('0.3','1.1'), mp.mpc('-0.7','0.9')]:
        gt = (a*t+b)/(c*t+d)
        S1,P1 = SP(t); S2,P2 = SP(gt)
        dF = lambda t: (t-3)*(t+1)   # det F'(t) = -sqrt2 (t-3)(t+1)/2 (QMLattice.det_Fp)
        for sgn in (1, -1):
            r = abs(dF(gt)/dF(t))**(sgn)
            print(f"  {name}: t={mp.nstr(t,4)} corr detF'^({4*sgn},{10*sgn}): S {mp.nstr(abs(S2/S1)/abs(c*t+d)**8*r**4,12)}, P {mp.nstr(abs(P2/P1)/abs(c*t+d)**20*r**10,12)}")
# (2) vanishing orders at CM points
print("(2) vanishing orders (log-ratio estimate with eps = 1e-3, 1e-4)")
cms = {"-4 (x=i+j, x^2=-1)": (0,1,1,0), "-3 (x=(1+j)/2)": (R(1,2),0,R(1,2),0), "-24 (x=2j+ij)": (0,0,2,1)}
for name, x in cms.items():
    t0 = fixpt(x)
    S0,P0 = SP(t0)
    e1, e2 = mp.mpf('1e-3'), mp.mpf('1e-4')
    Sa,Pa = SP(t0+e1*mp.mpc(1,0.37)); Sb,Pb = SP(t0+e2*mp.mpc(1,0.37))
    oS = mp.log(abs(Sa)/abs(Sb))/mp.log(10); oP = mp.log(abs(Pa)/abs(Pb))/mp.log(10)
    print(f"  CM {name}: tau0={mp.nstr(t0,12)} |S(tau0)|={mp.nstr(abs(S0),5)} |P(tau0)|={mp.nstr(abs(P0),5)} ord S ~ {mp.nstr(oS,6)} ord P ~ {mp.nstr(oP,6)}")
