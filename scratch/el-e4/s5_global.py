# Step 5: global test on toy instances. R0 = 2730^6 F(n) (Lean testR0, eta = 1), Theta0 = u/v random small
# (honest at contact primes: gcd(u, F(n)) = 1). By L5 reduce to R1 = squarefree part of R0, Th = Th0/s.
# For each m in the 64 signed divisors of 2730 with C_m locally soluble everywhere:
#   E : y^2 = x(x^2 + b x + ac), b = 2 m R1^2, ac = -m^2 R1^3 (m Th^2 - R1)   (C_m = psi-covering of class d = -m R1)
#   ellrank(E) + ellsaturation at 2 -> generators; C_m(Q) != empty  <=>  d in span{alpha(T) = ac, alpha(P_i) = x(P_i)} mod squares.
#   Decided if rank lower = upper bound. Cross-check: hyperellratpoints on the quartic (height <= HB).
import sys, json, random, time; sys.path.insert(0, "scratch/el-e4")
from fractions import Fraction as Fr
import cypari2; pari = cypari2.Pari(); pari.allocatemem(4*10**9)
import k0; from locsol import locsol, quartic
NINST = int(sys.argv[1]) if len(sys.argv) > 1 else 30
MCAP = int(sys.argv[2]) if len(sys.argv) > 2 else 8
HB = 2000
divs = sorted({s*d for d in range(1, 2731) if 2730 % d == 0 for s in (1, -1)}, key=lambda x: (abs(x), x))
def core(x):  # squarefree part of a nonzero rational
    x = Fr(str(x)); return int(pari.core(x.numerator * x.denominator))
def span_has(vecs, target):
    # F2 linear algebra on squarefree classes: bit 0 = sign, others = primes
    ps = sorted({int(p) for c in vecs + [target] for p in pari.factor(abs(c))[0]} if True else [])
    idx = {p: i + 1 for i, p in enumerate(ps)}
    def vec(c):
        r = 1 if c < 0 else 0
        for p in pari.factor(abs(c))[0]: r |= 1 << idx[int(p)]
        return r
    basis = {}
    for c in vecs:
        v = vec(c)
        while v:
            hbit = v.bit_length() - 1
            if hbit in basis: v ^= basis[hbit]
            else: basis[hbit] = v; break
    t = vec(target)
    while t:
        hbit = t.bit_length() - 1
        if hbit not in basis: return False
        t ^= basis[hbit]
    return True
random.seed(2026); out = []
for inst in range(NINST):
    n = random.randint(1, 40); R0 = k0.testR0(1, Fr(n))
    F = int(k0.F(Fr(n)))
    while True:
        u, v = random.randint(1, 10**4), random.randint(1, 10**4)
        if pari.gcd(u, v) == 1 and pari.gcd(u, F) == 1: break
    Th0 = Fr(u, v)
    R1 = core(R0); s = pari.sqrtint(int(R0 / R1)); s = int(s); assert R1 * s * s == R0
    Th = Th0 / s
    primes = sorted(set([2, 3, 5, 7, 11, 13]) | set(int(p) for p in pari.factor(abs(R1))[0]))
    obs = [int(p) for p in pari.factor(u)[0] if int(p) > 2 and R1 % int(p) and pari.kronecker(R1, int(p)) == -1]
    res = dict(n=n, Th0=str(Th0), R1=R1, obs=obs, curves=[])
    for m in divs:
        if not all(pari.kronecker(-m, p) == -1 for p in obs if m % p): continue
        f = quartic(m, Th, R1)
        if not all(locsol(f, p) is True for p in primes): continue
        # small primes of u (<= 13) already in primes; p | u, p >= 17 by L4; others by L2/L3
        if len(res["curves"]) >= MCAP: res["more"] = True; break
        t0 = time.time()
        b = 2*m*R1*R1; ac = -m*m*R1**3*(m*Th*Th - R1)
        E = pari.ellinit([0, str(b), 0, str(ac), 0])
        rk = pari.ellrank(E, 2)
        lo, hi, pts = int(rk[0]), int(rk[1]), rk[3]
        if len(pts): pts = pari.ellsaturation(E, pts, 2)
        d = core(-m*R1)
        alphas = [core(ac)] + [core(P[0]) for P in pts if P != [0] and P[0] != 0]
        hit = span_has(alphas, d) if d != 1 else True
        # point search on the integral quartic: scale h^2 = f(q), f with rational coeffs
        L = 1
        for c in f: L = L * Fr(c).denominator // int(pari.gcd(L, Fr(c).denominator))
        fi = [int(Fr(c) * L * L) for c in f]
        found = pari.hyperellratpoints(pari.Pol(list(reversed(fi))), HB)
        res["curves"].append(dict(m=m, rank_lo=lo, rank_hi=hi, inAlphaImage=bool(hit),
                                  decided=(lo == hi and len(pts) >= lo) or hit, ngens=len(pts), shaJ_s=int(pari.ellrank(pari.ellinit([0, str(-2*f[2]), 0, str(f[2]*f[2] - 4*f[4]*f[0]), 0]))[2]), pts_HB=len(found), sec=round(time.time()-t0, 1)))
    out.append(res); print(json.dumps(res), flush=True)
json.dump(out, open("scratch/el-e4/s5_out.json", "w"))
