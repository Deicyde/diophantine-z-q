# Numerical check of TwistTransportCd's consequence: for d, D = -m, S Heegner reps of level 32 d^2,
# Z_Q = sum_a (a/d) (x,y)(tau_Q + a/d) on 32a1 : y^2 = x^3 + 4x (x0-32's eta quotients).
# Claim: sigma(Z_Q) = eps_sigma Z_{pi Q}, eps = sigma(sqrt d)/sqrt d. Consequences checked:
#   prod_Q (X - x(Z_Q)) and prod_Q (X - sqrt(d) y(Z_Q)) have coefficients in K = Q(sqrt(-m)).
import sys, cypari2
pari = cypari2.Pari(); pari.set_real_precision(250)
d = int(sys.argv[1]); m = int(sys.argv[2]); N = 32*d*d; D = -m
E = pari.ellinit([0,0,0,4,0])
def xy(t):
    e = lambda k: pari.eta(k*t, 1)
    x = e(2)**2*e(16)/(e(4)*e(32)**2) + 2
    y = -(e(8)**4*e(16)**2/(e(4)**2*e(32)**4))
    return [x, y]
# beta with beta^2 = D mod 4N
beta = next(b for b in range(2*N) if (b*b - D) % (4*N) == 0)
# forms [A,B,C], N | A, B = beta mod 2N, B^2-4AC = D; classify by reduced SL2 form
reps = {}
for k in range(1, 400):
    A = N*k
    for B in range(beta - 2*N*3, beta + 2*N*3 + 1, 2*N):
        if (B*B - D) % (4*A) == 0:
            C = (B*B - D)//(4*A)
            red = pari.qfbred(pari.Qfb(A, B, C))
            key = str(red)
            if key not in reps: reps[key] = (A, B, C)
    if len(reps) >= pari.qfbclassno(D): break
print("beta", beta, "classes", len(reps), "h", pari.qfbclassno(D))
Zs = []
for key, (A, B, C) in reps.items():
    tau = (-B + pari.sqrt(D))/(2*A)
    Z = [0]
    for a in range(d):
        ch = int(pari.kronecker(a, d))
        if ch == 0: continue
        P = xy(tau + pari(a)/d)
        Z = pari.elladd(E, Z, pari.ellmul(E, P, ch))
    Zs.append(Z)
    print(key, "Z =", [pari.precision(c, 15) for c in Z] if len(Z) == 2 else Z)
X = pari('X')
px = pari(1); py = pari(1)
for Z in Zs:
    px *= (X - Z[0]); py *= (X - pari.sqrt(d)*Z[1])
for name, p in (("x", px), ("sqrt(d) y", py)):
    for i in range(len(Zs)):
        c = pari.polcoef(p, i)
        q = pari.algdep(c, 2); print("   value", pari.precision(c, 30))
        print(name, "coef", i, "algdep:", q, " disc factor:", pari.factor(pari.poldisc(q)) if pari.poldegree(q) == 2 else "")
