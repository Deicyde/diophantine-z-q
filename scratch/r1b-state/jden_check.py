"""r1b-state: where does jDen(Omega(tau)) = (sum_even theta_m^8)^5 vanish on N5's QM curve?
Checks the x/0 trap of the review: at the disc -3 CM point (pi = infinity) jDen = 0, so Lean's
jNum/jDen is 0 there; at the disc -4 point (pi = 0) jNum = 0 but jDen != 0; at the disc -24 point
and at sample points both are nonzero.  Omega(tau) and theta constants re-implemented from
pkg-I1's definitions (as in scratch/g0-thetapoint/theta_check.py).
Run: ~/pyenv/bin/python -I jden_check.py"""
import sympy as sp, mpmath as mp
mp.mp.dps = 30
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
def theta(ch, Om, N=18):
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
def fixpt(x):
    g_ = iota(x); A1, B1, C1, D1 = [mp.mpf(sp.N(g_[r,c], 40)) for r,c in ((0,0),(0,1),(1,0),(1,1))]
    d_ = (D1-A1)**2 + 4*B1*C1
    w = (-(D1-A1) + mp.sqrt(d_))/(2*C1)
    return w if mp.im(w) > 0 else (-(D1-A1) - mp.sqrt(d_))/(2*C1)
def report(name, w):
    Om = Omf(w); th = [theta(ch, Om) for ch in ev]
    S = mp.fsum([x**8 for x in th]); P = mp.fprod(th)
    jden = S**5; jnum = 3779136*P**4
    print(f"{name:28s} tau = {mp.nstr(w, 12):34s} |sum th^8| = {mp.nstr(abs(S), 5):10s} "
          f"|prod th| = {mp.nstr(abs(P), 5):10s} jNum/jDen = " +
          (mp.nstr(jnum/jden, 10) if abs(S) > mp.mpf(10)**-15 else "(jDen = 0)"))
report("disc -3  (x = (1+j)/2)", fixpt((R(1,2),0,R(1,2),0)))
report("disc -4  (x = i+j)", fixpt((0,1,1,0)))
report("disc -24 (x = mu = 2j+ij)", fixpt((0,0,2,1)))
for w in (mp.mpc(0,1), mp.mpc('0.3','0.7'), mp.mpc('1.3932949171603','0.8693197409124'),
          mp.mpc('-0.5','1.2'), mp.mpc('2','0.5')):
    report("sample", w)
