"""g0-thetapoint: numerical sanity checks for ThetaRatiosAlgebraic and thetaConst_odd at the
CM point tau_-24 (fixed point of iota(mu), mu = 2j+ij) of N5's QM datum.  Own computation
(the QM datum and Omega(tau) follow pkg-I1's definitions, re-implemented here).
Run: ~/pyenv/bin/python -I theta_check.py"""
import sympy as sp, mpmath as mp, cypari2
pari = cypari2.Pari(); pari.set_real_precision(220)
mp.mp.dps = 220
R = sp.Rational
s2 = sp.sqrt(2)
basis = [(1,0,0,0), (0,1,0,0), (R(1,2),0,R(1,2),0), (0,R(1,2),0,R(1,2))]
mu = (0,0,2,1)
def iota(x):
    x0,x1,x2,x3 = [sp.nsimplify(t) for t in x]
    Mi = sp.Matrix([[s2,0],[0,-s2]]); Mj = sp.Matrix([[0,-3],[1,0]])
    return x0*sp.eye(2) + x1*Mi + x2*Mj + x3*Mi*Mj
tau = sp.symbols('tau'); v = sp.Matrix([tau, 1])
cols = [iota(b)*v for b in basis]
Pinv = sp.Matrix([[-1,1],[1,-2]]).inv()
E1 = sp.Matrix.hstack(cols[0], cols[1]); F1 = sp.Matrix.hstack(cols[2], cols[3]) * Pinv
Omf = sp.lambdify(tau, F1.inv()*E1, 'mpmath')     # pkg-I1's Omega(tau) = (F0 P^-1)^-1 E
def theta(ch, Om, N=34):
    (a1,a2),(b1,b2) = ch
    s = mp.mpc(0)
    for n1 in range(-N, N+1):
        for n2 in range(-N, N+1):
            x1 = n1 + mp.mpf(a1)/2; x2 = n2 + mp.mpf(a2)/2
            Q = x1*x1*Om[0,0] + 2*x1*x2*Om[0,1] + x2*x2*Om[1,1]
            s += mp.exp(1j*mp.pi*(Q + x1*b1 + x2*b2))
    return s
chars = [((a1,a2),(b1,b2)) for a1 in (0,1) for a2 in (0,1) for b1 in (0,1) for b2 in (0,1)]
odd = lambda ch: (ch[0][0]*ch[1][0] + ch[0][1]*ch[1][1]) % 2 == 1
# fixed point of iota(mu) in the upper half plane
g = iota(mu); A_, B_, C_, D_ = [mp.mpf(sp.N(g[r,s], 240)) for r,s in ((0,0),(0,1),(1,0),(1,1))]
disc = (D_-A_)**2 + 4*B_*C_
z = (-(D_-A_) + mp.sqrt(disc))/(2*C_)
if mp.im(z) < 0: z = (-(D_-A_) - mp.sqrt(disc))/(2*C_)
print("tau_-24 =", mp.nstr(z, 20))
Om = Omf(z)
th = {ch: theta(ch, Om) for ch in chars}
print("max |theta_odd| =", mp.nstr(max(abs(th[ch]) for ch in chars if odd(ch)), 5))
ev = [ch for ch in chars if not odd(ch)]
print("min |theta_even| =", mp.nstr(min(abs(th[ch]) for ch in ev), 10))
P = mp.fprod([th[ch] for ch in ev]); S = mp.fsum([th[ch]**8 for ch in ev])
print("j_theta =", mp.nstr(3779136*P**4/S**5, 25), " (target -16/27 =", mp.nstr(mp.mpf(-16)/27, 25), ")")
print("Im Omega eigenvalues:", [mp.nstr(e, 6) for e in mp.eig(mp.matrix([[mp.im(Om[0,0]), mp.im(Om[0,1])], [mp.im(Om[1,0]), mp.im(Om[1,1])]]))[0]])
m0 = ev[0]
for ch in ev[1:]:
    r = (th[ch]/th[m0])**4
    found = None
    for deg in (2, 4, 8, 16, 24, 32):
        pol = pari.algdep(pari(f"({mp.nstr(mp.re(r), 210)}) + ({mp.nstr(mp.im(r), 210)})*I".replace("e", "E")), deg)
        coeffs = [int(c) for c in pari.Vec(pol)]
        val = mp.polyval(coeffs, r)
        h = max(abs(c) for c in coeffs)
        if abs(val) < mp.mpf(10)**-150 and mp.log10(h) < 40:
            found = (pari.poldegree(pol), int(mp.log10(h)) + 1, str(pari.factor(pol)[0][0])[:80]); break
    print(ch, "(theta_m/theta_m0)^4:", f"satisfies an integer polynomial of degree {found[0]}, coefficients < 10^{found[1]} (residual < 1e-150)" if found else "no relation of degree <= 32 found")

# ---- a non-CM fibre: u = 1, J(1) = -57600 F(1)^2 / G(1)^6; find tau = i t with j_theta(i t) = J(1) ----
u = R(1)
Fu = u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60); Gu = 7*u**2 + 300*u + 3600
Ju = R(-57600)*Fu**2/Gu**6
print("J(1) =", Ju, "=", mp.nstr(mp.mpf(Ju.p)/Ju.q, 20))
def jt(t, N=34):
    Om_ = Omf(mp.mpc(0, t)); ths = [theta(ch, Om_, N) for ch in ev]
    return 3779136*mp.fprod(ths)**4/mp.fsum([x**8 for x in ths])**5
mp.mp.dps = 40
def fixpt(x):
    g_ = iota(x); A1, B1, C1, D1 = [mp.mpf(sp.N(g_[r,s_], 60)) for r,s_ in ((0,0),(0,1),(1,0),(1,1))]
    d_ = (D1-A1)**2 + 4*B1*C1
    w = (-(D1-A1) + mp.sqrt(d_))/(2*C1)
    return w if mp.im(w) > 0 else (-(D1-A1) - mp.sqrt(d_))/(2*C1)
def jz(w, N=20):
    Om_ = Omf(w); ths = [theta(ch, Om_, N) for ch in ev]
    return 3779136*mp.fprod(ths)**4/mp.fsum([x**8 for x in ths])**5
t4 = fixpt((0,1,1,0))
print("tau_-4 =", mp.nstr(t4, 15), " j_theta =", mp.nstr(jz(t4), 5))
target = mp.mpf(Ju.p)/Ju.q
best = None
for rad in ('0.05', '0.1', '0.2', '0.3'):
    for k in range(16):
        w = t4 + mp.mpf(rad)*mp.expjpi(mp.mpf(k)/8)
        if mp.im(w) <= 0.05: continue
        d_ = abs(jz(w) - target)
        if best is None or d_ < best[0]: best = (d_, w)
print("start", mp.nstr(best[1], 10), "residual", mp.nstr(best[0], 5))
w1 = mp.findroot(lambda w: jz(w) - target, best[1])
print("tau_u =", mp.nstr(w1, 25), " |j_theta - J(1)| =", mp.nstr(abs(jz(w1, 30) - target), 5))
# theta ratios at tau_u, at high precision
mp.mp.dps = 220; pari.set_real_precision(220)
w1 = mp.findroot(lambda w: jz(w, 34) - target, w1)
Om1 = Omf(w1); th1 = {ch: theta(ch, Om1) for ch in chars}
print("at tau_u: max |theta_odd| =", mp.nstr(max(abs(th1[ch]) for ch in chars if odd(ch)), 5),
      " min |theta_even| =", mp.nstr(min(abs(th1[ch]) for ch in ev), 8))
for ch in ev[1:4]:
    r = (th1[ch]/th1[m0])**4
    found = None
    for deg in (2, 4, 8, 12, 16, 24):
        pol = pari.algdep(pari(f"({mp.nstr(mp.re(r), 210)}) + ({mp.nstr(mp.im(r), 210)})*I".replace("e", "E")), deg)
        coeffs = [int(c) for c in pari.Vec(pol)]
        h = max(abs(c) for c in coeffs)
        if abs(mp.polyval(coeffs, r)) < mp.mpf(10)**-150 and mp.log10(h) < 60:
            found = (pari.poldegree(pol), int(mp.log10(h)) + 1); break
    print(ch, "(theta_m/theta_m0)^4 at tau_u:", f"integer polynomial of degree {found[0]}, coefficients < 10^{found[1]}" if found else "no relation of degree <= 24 found")

# ---- stability: redo at 420 digits; a genuine relation keeps its coefficients and its residual
# drops to ~1e-400; a spurious one (expected residual ~ H^-5.5 for 13 coefficients of size H in C)
# does not survive ----
mp.mp.dps = 430; pari.set_real_precision(430)
w2 = mp.findroot(lambda w: jz(w, 46) - target, w1)
Om2 = Omf(w2); th2 = {ch: theta(ch, Om2, 46) for ch in ev}
for ch in ev[1:4]:
    r = (th2[ch]/th2[m0])**4
    pol = pari.algdep(pari(f"({mp.nstr(mp.re(r), 420)}) + ({mp.nstr(mp.im(r), 420)})*I".replace("e", "E")), 12)
    coeffs = [int(c) for c in pari.Vec(pol)]
    h = max(abs(c) for c in coeffs)
    print(ch, "420 digits, degree 12:", f"coefficients < 10^{int(mp.log10(h)) + 1}",
          "residual", mp.nstr(abs(mp.polyval(coeffs, r)), 5), "irreducible" if pari.polisirreducible(pol) else "reducible",
          "poly:", str(pol)[:120])
