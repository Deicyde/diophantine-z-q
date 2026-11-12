"""pkg-I1: explicit modular embedding for N5's QM datum (B=(2,-3), O, mu=2j+ij) and numerical checks
of the analytic F1/A2 leaf.  Own computation; no source text copied.
Run: ~/pyenv/bin/python -I qm_embed.py"""
import sympy as sp, mpmath as mp
mp.mp.dps = 30
s2 = sp.sqrt(2)
# quaternion arithmetic in coordinates (x0,x1,x2,x3) for 1,i,j,k=ij with i^2=2, j^2=-3
a, c = 2, -3
def qmul(x, y):
    x0,x1,x2,x3 = x; y0,y1,y2,y3 = y
    return (x0*y0 + a*x1*y1 + c*x2*y2 - a*c*x3*y3,
            x0*y1 + x1*y0 - c*x2*y3 + c*x3*y2,
            x0*y2 + x2*y0 + a*x1*y3 - a*x3*y1,
            x0*y3 + x3*y0 + x1*y2 - x2*y1)
def conj(x): return (x[0], -x[1], -x[2], -x[3])
def trd(x): return 2*x[0]
R = sp.Rational
basis = [(1,0,0,0), (0,1,0,0), (R(1,2),0,R(1,2),0), (0,R(1,2),0,R(1,2))]
mu = (0,0,2,1)
assert qmul(mu,mu) == (-6,0,0,0)
muinv = tuple(-R(1,6)*t for t in mu)
# sanity: associativity and i^2, j^2, k = ij anticommutation
I_, J_, K_ = (0,1,0,0),(0,0,1,0),(0,0,0,1)
assert qmul(I_,I_)==(2,0,0,0) and qmul(J_,J_)==(-3,0,0,0) and qmul(I_,J_)==K_ and qmul(J_,I_)==(0,0,0,-1)
gram = sp.Matrix(4,4,lambda r,s: trd(qmul(qmul(muinv,basis[r]),conj(basis[s]))))
print("Gram Trd(mu^-1 x ybar):", gram.tolist(), "det", gram.det())
assert gram.tolist() == [[0,0,-1,1],[0,0,1,-2],[1,-1,0,0],[-1,2,0,0]] and gram.det() == 1
# real embedding
def iota(x):
    x0,x1,x2,x3 = [sp.nsimplify(t) for t in x]
    Mi = sp.Matrix([[s2,0],[0,-s2]]); Mj = sp.Matrix([[0,-3],[1,0]])
    return x0*sp.eye(2) + x1*Mi + x2*Mj + x3*Mi*Mj
assert iota(I_)**2 == 2*sp.eye(2) and iota(J_)**2 == -3*sp.eye(2)
for x in basis + [mu]:
    for y in basis + [mu]:
        assert sp.simplify(iota(qmul(x,y)) - iota(x)*iota(y)) == sp.zeros(2)
# lattice and period matrix
tau = sp.symbols('tau')
v = sp.Matrix([tau, 1])
cols = [iota(b)*v for b in basis]   # images of 1, i, (1+j)/2, (i+ij)/2
# symplectic basis: E(e_a, f_b) block P = [[-1,1],[1,-2]] for e=(b1,b2), f=(b3,b4).
P = sp.Matrix([[-1,1],[1,-2]])
# new f' = f * (P^-1)^T-combination so that E(e_a, f'_b) = delta
Pinv = P.inv()
E1 = sp.Matrix.hstack(cols[0], cols[1])
F0 = sp.Matrix.hstack(cols[2], cols[3])
F1 = F0 * Pinv            # f'_b = sum_c f_c (P^-1)_{c b}: E(e_a,f'_b) = sum_c P_{ac} (P^-1)_{cb}
for name, Om in (("E^-1 F", E1.inv()*F1), ("F^-1 E", F1.inv()*E1)):
    Om = sp.simplify(Om)
    t0 = 0.3 + 1.1j
    On = [[complex(Om[r,s].subs(tau, t0)) for s in range(2)] for r in range(2)]
    sym = abs(On[0][1]-On[1][0]); im = [[On[r][s].imag for s in range(2)] for r in range(2)]
    pd = im[0][0] > 0 and im[0][0]*im[1][1]-im[0][1]*im[1][0] > 0
    print(name, "=", Om.tolist(), " symmetric err", sym, " Im posdef", pd)

# ---- numerical checks of the analytic leaf ----
Omf = sp.lambdify(tau, F1.inv()*E1, 'mpmath')
def Omega(t):
    M = Omf(t); return [[M[0,0], M[0,1]], [M[1,0], M[1,1]]]
def theta(ch, Om, N=18):
    (a1,a2),(b1,b2) = ch
    s = mp.mpc(0)
    for n1 in range(-N, N+1):
        for n2 in range(-N, N+1):
            x1 = n1 + mp.mpf(a1)/2; x2 = n2 + mp.mpf(a2)/2
            Q = x1*x1*Om[0][0] + 2*x1*x2*Om[0][1] + x2*x2*Om[1][1]
            s += mp.exp(1j*mp.pi*(Q + x1*b1 + x2*b2))
    return s
chars = [((a1,a2),(b1,b2)) for a1 in (0,1) for a2 in (0,1) for b1 in (0,1) for b2 in (0,1)]
even = [ch for ch in chars if (ch[0][0]*ch[1][0] + ch[0][1]*ch[1][1]) % 2 == 0]
assert len(even) == 10
def jtheta_parts(t):
    Om = Omega(t)
    im = [[mp.im(Om[r][s]) for s in range(2)] for r in range(2)]
    assert abs(Om[0][1]-Om[1][0]) < mp.mpf(10)**-20 and im[0][0] > 0 and im[0][0]*im[1][1]-im[0][1]**2 > 0
    th = [theta(ch, Om) for ch in even]
    return mp.fprod(th)**4, mp.fsum([x**8 for x in th])**5
def jtheta(t):
    P, S = jtheta_parts(t); return 3779136*P/S
def moeb(g, t):
    return (g[0][0]*t + g[0][1])/(g[1][0]*t + g[1][1])
def iotan(x):
    M = iota(x); return [[mp.mpf(sp.N(M[r,s], 40)) for s in range(2)] for r in range(2)]
els = {"i+j (order 4)": (0,1,1,0), "(1+j)/2 (order 6)": (R(1,2),0,R(1,2),0), "mu=2j+ij (nrd 6)": mu,
       "1+i+j (nrd 2)": (1,1,1,0), "j (nrd 3)": (0,0,1,0), "2+i+j+... unit": None}
# a non-torsion unit of O^1: search small elements of O with nrd 1 and |trace| > 2
def nrd(x): return x[0]**2 - a*x[1]**2 - c*x[2]**2 + a*c*x[3]**2
found = None
for n0 in range(-6,7):
  for n1 in range(-6,7):
    for n2 in range(-6,7):
      for n3 in range(-6,7):
        x = tuple(sum(R(nn)*basis[k][m] for k, nn in enumerate((n0,n1,n2,n3))) for m in range(4))
        if nrd(x) == 1 and abs(trd(x)) > 2:
            found = x; break
      if found: break
    if found: break
  if found: break
els["2+i+j+... unit"] = found
print("non-torsion unit of O^1:", found, "trace", trd(found))
t0 = mp.mpc('0.31', '1.13')
j0 = jtheta(t0)
print("j_theta(t0) =", mp.nstr(j0, 20))
for name, x in els.items():
    g = iotan(x)
    assert g[0][0]*g[1][1]-g[0][1]*g[1][0] > 0
    j1 = jtheta(moeb(g, t0))
    print(f"  invariance under {name}: |j(g t0) - j(t0)| = {mp.nstr(abs(j1-j0), 5)}")
def fixpt(x):
    g = iotan(x); A_, B_, C_, D_ = g[0][0], g[0][1], g[1][0], g[1][1]
    # C z^2 + (D-A) z - B = 0, root in upper half plane
    disc = (D_-A_)**2 + 4*B_*C_
    z = (-(D_-A_) + mp.sqrt(disc))/(2*C_)
    if mp.im(z) < 0: z = (-(D_-A_) - mp.sqrt(disc))/(2*C_)
    return z
for name, x, target in (("tau_-4", (0,1,1,0), 0), ("tau_-3", (R(1,2),0,R(1,2),0), None), ("tau_-24", mu, mp.mpf(-16)/27)):
    z = fixpt(x)
    P, S = jtheta_parts(z)
    print(f"{name} = {mp.nstr(z, 15)}: 3779136*prod^4 = {mp.nstr(3779136*P, 8)}, sum^5 = {mp.nstr(S, 8)}",
          "" if target is None else f"j = {mp.nstr(3779136*P/S, 20)} target {mp.nstr(target, 10)}")

# ---- further checks ----
# (a) the non-torsion unit, at a point where both t0 and g t0 have moderate imaginary part
gU = iotan(els["2+i+j+... unit"])
t1 = fixpt(els["(1+j)/2 (order 6)"]) + mp.mpc('0.05','0.02')   # near tau_-3
for N in (18, 30):
    th_old = theta
    def jthN(t, N=N):
        Om = Omega(t); th = [theta(ch, Om, N) for ch in even]
        return 3779136*mp.fprod(th)**4/mp.fsum([x**8 for x in th])**5
    tA = mp.mpc('0.2','0.9'); tB = moeb(gU, tA)
    print(f"N={N}: Im(tA)={mp.nstr(mp.im(tA),5)} Im(g tA)={mp.nstr(mp.im(tB),5)}; |j(g tA)-j(tA)| = {mp.nstr(abs(jthN(tB)-jthN(tA)),5)}")
# (b) behaviour near tau_-3: |j| should blow up
z3 = fixpt(els["(1+j)/2 (order 6)"])
for eps in ('0.1','0.03','0.01'):
    print(f"near tau_-3, eps={eps}: |j_theta| = {mp.nstr(abs(jtheta(z3 + mp.mpf(eps)*1j)), 8)}")
# (c) disc -19 point: x in O with x^2 - x + 5 = 0; expect j = 81/64 (value attributed to Lin-Yang, igusa_check.py)
sol = None
for n0 in range(-4,5):
  for n1 in range(-4,5):
    for n2 in range(-4,5):
      for n3 in range(-4,5):
        x = tuple(sum(R(nn)*basis[k][m] for k, nn in enumerate((n0,n1,n2,n3))) for m in range(4))
        if trd(x) == 1 and nrd(x) == 5: sol = x; break
      if sol: break
    if sol: break
  if sol: break
z19 = fixpt(sol)
print("disc -19 element", sol, "fixed point", mp.nstr(z19, 12), "j_theta =", mp.nstr(jtheta(z19), 20), "81/64 =", mp.nstr(mp.mpf(81)/64, 20))
