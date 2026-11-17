# Independent numeric test of the Lean leaf TYZThm33 (TYZ Theorem 3.3 on the eta model of X0(32)).
# Pure Python + mpmath.  Points are handled as elliptic logarithms z(tau) = sum a_m q^m / m  (mod Lambda),
# which is the logarithm of phiC(tau) = (x(tau), y(tau)) for omega = dx/(2y) (checked: q dx/dq = 2 f y).
# [i](x,y) = (-x, i y) acts on logarithms as multiplication by i  (d(-x)/(2 i y) = i dx/(2y)).
import sys
from math import gcd, isqrt
from mpmath import mp, mpf, mpc, exp, pi, sqrt, nint, quad, inf, re, im, fabs
mp.dps = 40

NMAX = 20000
# a_m of 32a: f = q * g(q^4), g(t) = prod (1-t^n)^2 (1-t^{2n})^2
K = NMAX // 4 + 2
g = [0]*K; g[0] = 1
def mult_euler(c, d):
    n = 1
    while d*n < K:
        k = d*n
        for i in range(K-1, k-1, -1):
            c[i] -= c[i-k]
        n += 1
for d in (1, 1, 2, 2):
    mult_euler(g, d)
def a(m):
    return g[(m-1)//4] if m % 4 == 1 else 0

def zphi(tau):
    q = exp(2*pi*mpc(0, 1)*tau)
    aq = abs(q)
    assert aq < 1
    q4 = q**4
    s = mpc(0); qq = q; m = 1
    while True:
        am = g[(m-1)//4]
        if am: s += am*qq/m
        qq *= q4; m += 4
        if abs(qq) < mpf(10)**(-36): break
        if m >= NMAX: raise RuntimeError("series too slow: |q|=%s" % aq)
    return s

# period lattice from modular symbols
def moeb(M, tau):
    a_, b_, c_, d_ = M
    return (a_*tau + b_)/(c_*tau + d_)
def period(M):
    a_, b_, c_, d_ = M
    tau = mpc(-mpf(d_)/c_, mpf(1)/abs(c_))
    return zphi(moeb(M, tau)) - zphi(tau)

pers = []
for (a_, d_) in [(1, 1), (3, 11), (5, 13), (7, 23), (9, 25), (15, 15)]:
    assert (a_*d_ - 1) % 32 == 0
    pers.append(period((a_, (a_*d_-1)//32, 32, d_)))
from mpmath import gamma
om1q = quad(lambda x: 1/sqrt(x**3 + 4*x), [0, 1, inf])
om1 = gamma(mpf(1)/4)**2/(2*sqrt(2*pi))
print('quad vs gamma:', mp.nstr(om1q-om1, 5))
lam = om1*(1+mpc(0, 1))/2
print("real period om1 =", om1)
print("periods / lam (should be Gaussian integers generating Z[i]):")
for p in pers:
    print("   ", mp.nstr(p/lam, 12))

I = mpc(0, 1)
def tors_coords(z):
    w = z/lam
    return re(w), im(w)
def is_torsion(z, maxden=64, tol=mpf(10)**(-28)):
    u, v = tors_coords(z)
    for dd in range(1, maxden+1):
        if fabs(u*dd - nint(u*dd)) < tol and fabs(v*dd - nint(v*dd)) < tol:
            return dd
    return 0

def reduce_form(A, B, C):
    while True:
        if abs(B) > A:
            k = (B + A) // (2*A) if True else 0
            # B -> B - 2 A k
            k = (B + A) // (2*A)
            C = A*k*k - B*k + C
            B = B - 2*A*k
        if A > C:
            A, B, C = C, -B, A
            continue
        break
    if abs(B) == A or A == C:
        B = abs(B)
    return (A, B, C)

def heegner_forms(D, beta, h, amax=4000):
    reps = {}
    for a_ in range(1, amax+1):
        A = 32*a_
        for j in range(a_):
            B = beta + 64*j
            if (B*B - D) % (4*A): continue
            C = (B*B - D)//(4*A)
            if gcd(gcd(A, B), C) != 1 or gcd(gcd(a_, B), 32*C) != 1: continue
            key = reduce_form(A, B, C)
            if key not in reps:
                reps[key] = (A, B, C)
        if len(reps) == h: return reps
    raise RuntimeError("only %d of %d classes" % (len(reps), h))

def classno(D):
    h = 0
    b = D % 2
    while 3*b*b <= -D:
        q = (b*b - D)//4
        a_ = max(b, 1)
        while a_*a_ <= q:
            if q % a_ == 0:
                c = q//a_
                if gcd(gcd(a_, b), c) == 1:
                    h += 1 if (a_ == b or a_*a_ == q or b == 0) else 2
            a_ += 1
        b += 2
    return h

def kron(a_, n_):  # Kronecker symbol (a/n), n > 0 odd here
    assert n_ > 0 and n_ % 2 == 1
    a_ %= n_; r = 1
    while a_:
        while a_ % 2 == 0:
            a_ //= 2
            if n_ % 8 in (3, 5): r = -r
        a_, n_ = n_, a_
        if a_ % 4 == 3 and n_ % 4 == 3: r = -r
        a_ %= n_
    return r if n_ == 1 else 0

def represented(Q, D):
    A, B, C = Q
    for s in range(1, 200):
        for x in range(-s, s+1):
            for y in (s-abs(x), -(s-abs(x))):
                m = A*x*x + B*x*y + C*y*y
                if m > 0 and gcd(m, 2*D) == 1: return m
    raise ValueError

def gchar(e, Q, D):
    """character of K(sqrt e)/K on the class of Q: (e/m), m odd represented, coprime to 2D."""
    if e == 1: return 1
    m = represented(Q, D)
    # (e/m) with m odd positive: Jacobi symbol of the integer e (sign of e matters)
    return kron(e, m)

def tau_of(Q, D):
    A, B, C = Q
    return mpc(-mpf(B), sqrt(mpf(-D)))/(2*A)

def delta7(n):
    for d in range(128):
        if (d*d + n) % 128 == 0: return d

def sums(D, beta, es):
    h = classno(D)
    reps = heegner_forms(D, beta, h)
    out = {e: mpc(0) for e in es}
    for Q in reps.values():
        z = zphi(tau_of(Q, D))
        for e in es:
            out[e] += gchar(e, Q, D)*z
    return out, h

def P1(d0):
    """log of P_1(d0) (trivial character) up to torsion and sign conventions as in the leaf."""
    if d0 % 8 == 7:
        S, h = sums(-d0, delta7(d0), [1])
        return S[1]
    S, h = sums(-64*d0, -8, [1, d0])
    return (S[1] - I*S[d0])/4

def find_multiple(z, base, units, rng):
    hits = []
    for u in units:
        for m in range(-rng, rng+1):
            if is_torsion(z - m*u*base, 64):
                hits.append((m, u))
    return hits

def Lval(d):
    """L(E_d,1) for odd d = 1,3 mod 8 (root number +1): 2 sum a_n chi(n)/n exp(-2 pi n/sqrt(N)), N = 32 d^2."""
    N = 32*d*d
    x = exp(-2*pi/sqrt(mpf(N)))
    s = mpf(0); n_ = 1; xp = x
    while n_ < NMAX:
        an = a(n_)
        if an and gcd(n_, d) == 1:
            s += an*kron(d, n_)*xp/n_
        n_ += 4; xp *= x**4
        if xp < mpf(10)**(-34): break
    else:
        raise RuntimeError("L series too slow")
    return 2*s

omint = quad(lambda x: 1/sqrt(x**3 - x), [1, 2, inf])
def lcalSq(m):
    k = 0; t = m; p = 2
    while t > 1:
        if t % p == 0:
            k += 1
            while t % p == 0: t //= p
        p += 1
    return Lval(m)/(mpf(2)**(2*k-3)*(2/sqrt(mpf(m)))*omint)

if __name__ == "__main__":
    which = sys.argv[1:]
    if "lcal" in which:
        for m in (1, 3, 11, 17, 19, 33, 41):
            print("lcalSq(%d) = %s" % (m, mp.nstr(lcalSq(m), 15)))
    if "five" in which:
        for n in (5, 13, 21, 29, 37):
            D = -64*n
            divs = [e for e in range(1, n+1) if n % e == 0]
            S, h = sums(D, -8, divs)
            print("n = %d, h(-64n) = %d" % (n, h))
            for e in divs:
                P = (S[e] - I*S[n//e])/4
                Palt = (S[e] + I*S[n//e])/4
                print("   e=%d (chi <-> K(sqrt %d)): project sign (1-[i]): torsion den=%d ; other sign (1+[i]): torsion den=%d ; coords %s"
                      % (e, e, is_torsion(16*P), is_torsion(16*Palt), mp.nstr(tors_coords(P)[0], 8) + "," + mp.nstr(tors_coords(P)[1], 8)))

def show(z):
    u, v = tors_coords(z)
    return "(%s, %s)" % (mp.nstr(u, 12), mp.nstr(v, 12))

if __name__ == "__main__" and "five2" in sys.argv:
    for n in (5, 13, 21, 29, 37, 53, 61, 85):
        D = -64*n
        divs = [e for e in range(1, n+1) if n % e == 0]
        S, h = sums(D, -8, divs)
        print("n = %d, h(-64n) = %d" % (n, h))
        for e in divs:
            P = (S[e] - I*S[n//e])/4
            Palt = (S[e] + I*S[n//e])/4
            print("   e=%-3d project sign z=(1-[i])P: 16*P_chi torsion-den=%d coords(P)=%s | other sign (1+[i]): torsion-den=%d coords=%s"
                  % (e, is_torsion(16*P), show(P), is_torsion(16*Palt), show(Palt)))

def rad_star(d1):   # d1* = (-1)^{(d1-1)/2} d1
    return d1 if d1 % 4 == 1 else -d1

def h2(n):
    # 2-rank of Cl(Q(sqrt -n)) = t - 1, t = number of primes dividing disc
    ps = [p for p in range(2, n+1) if n % p == 0 and all(p % r for r in range(2, isqrt(p)+1))]
    t = len(ps) + (1 if n % 4 != 3 else 0)   # 2 ramifies unless -n = 1 mod 4
    return t - 1

def Pchi(n, d1):
    """log of P_chi for chi = chi_{d0,d1} as in the Lean leaf (up to the sign chi(a0) and torsion)."""
    if n % 8 == 7:
        e = rad_star(d1)
        S, h = sums(-n, delta7(n), [1, e]) if d1 != 1 else sums(-n, delta7(n), [1])
        return S[e] if d1 != 1 else S[1]
    # n = 5 mod 8: chi <-> K(sqrt d1); P_chi = (T_chi - i T_{chi kappa})/4, chi*kappa <-> K(sqrt(n/d1))
    S, h = sums(-64*n, -8, [d1, n//d1])
    return (S[d1] - I*S[n//d1])/4

def lcal(m):
    v = lcalSq(m)
    r = nint(sqrt(fabs(v)))
    assert fabs(v - r*r) < mpf(10)**(-20), (m, v)
    return int(r)

def test_pair(d0, d1):
    n = d0*d1
    assert n % 8 in (5, 7) and d0 % 8 in (5, 7) and d1 % 8 in (1, 3)
    P = Pchi(n, d1)
    B = Pchi(d0, 1)
    L = lcal(d1)
    lhs = (2**h2(d0))*P
    target = (2**h2(n))*L
    cls = "(%d,%d) mod 8" % (d0 % 8, d1 % 8)
    unit_expected = "+-i" if (d0 % 8 == 5 and d1 % 8 == 3) else "+-1"
    hits = []
    for name, u in (("+1", 1), ("-1", -1), ("+i", I), ("-i", -I)):
        for m in range(0, 4*max(target, 1) + 9):
            if is_torsion(16*(lhs - u*m*B)):
                hits.append((name, m))
    btors = is_torsion(16*B)
    ptors = is_torsion(16*P)
    print("n=%d=(%d)(%d) %s h2(n)=%d h2(d0)=%d Lcal(d1)=%d: P_1(d0) torsion=%s, P_chi torsion=%s; 2^h2(d0) P_chi = u*m*P_1(d0) mod tors for (u,m) in %s; leaf predicts u in %s, m=%d"
          % (n, d0, d1, cls, h2(n), h2(d0), L, bool(btors), bool(ptors), hits, unit_expected, target))
    sys.stdout.flush()

if __name__ == "__main__" and "pairs" in sys.argv:
    for (d0, d1) in [(7, 3), (5, 17), (5, 3), (13, 3), (5, 11), (7, 17), (7, 41), (15, 17), (5, 51), (85, 3), (23, 3), (13, 11), (29, 3), (31, 17), (21, 11), (37, 3), (5, 19)]:
        test_pair(d0, d1)

def to_class_maximal(Q, n):
    """image in Cl(-4n) (n = 1 mod 4) of the class of the form Q of disc -64n: find m odd coprime to 2n
    represented by Q, then identify the reduced form of disc -4n of an ideal of norm m... we use: the class
    is determined (up to inverse) by which reduced forms of disc -4n represent a small prime p represented by Q."""
    A, B, C = Q
    D = -64*n
    # find a prime p represented by Q, p coprime to 2D
    for s in range(1, 400):
        for x in range(-s, s+1):
            for y in (s-abs(x), -(s-abs(x))):
                p = A*x*x + B*x*y + C*y*y
                if p > 2 and gcd(p, 2*D) == 1 and all(p % r for r in range(2, isqrt(p)+1)):
                    # reduced form of disc -4n representing p: [p, b, c] with b^2 = -4n mod 4p
                    for b in range(0, 2*p, 2):
                        if (b*b + 4*n) % (4*p) == 0:
                            return frozenset([reduce_form(p, b, (b*b+4*n)//(4*p)), reduce_form(p, -b, (b*b+4*n)//(4*p))])
    raise ValueError

if __name__ == "__main__" and "lifts" in sys.argv:
    for n in (5, 13, 21, 29, 37):
        D = -64*n
        h = classno(D)
        reps = heegner_forms(D, -8, h)
        princ = reduce_form(1, 0, n)
        ker = []; allz = []
        for key, Q in reps.items():
            Z = zphi(tau_of(Q, D))
            kap = gchar(n, Q, D)     # character of K(sqrt n) = K(i)
            zc = Z - kap*I*Z         # log of z_n^{sigma_c} for the project's z_n = (1-[i]) f0(P_n)
            img = to_class_maximal(Q, n)
            allz.append((key, img, zc))
            if princ in img: ker.append((key, zc))
        base = ker[0][1]
        print("n=%d: h(-64n)=%d, kernel of Pic(O_{-64n}) -> Cl(-4n) has %d classes" % (n, h, len(ker)))
        for key, zc in ker:
            print("   class %s: z^gamma - z coords = %s, torsion den = %d" % (key, show(zc - base), is_torsion(zc - base)))
        # complex conjugation check for the trace: 2 Re

if __name__ == "__main__" and "minus" in sys.argv:
    from mpmath import conj
    for d0 in (7, 15, 23, 31, 39, 47, 5, 13, 21, 29, 37, 53):
        B = Pchi(d0, 1)
        s = B + conj(B)      # log of P + conj(P); should be torsion if P is in the minus part mod torsion
        dlt = B - conj(B)    # should be torsion if P were in the plus part
        print("d0=%d (mod 8: %d): P_1 torsion: %s; P_1 + conj(P_1) torsion den=%d coords=%s ; P_1 - conj(P_1) torsion den=%d"
              % (d0, d0 % 8, bool(is_torsion(16*B)), is_torsion(s), show(s), is_torsion(dlt)))

if __name__ == "__main__" and "pairs2" in sys.argv:
    for (d0, d1) in [(55, 3), (15, 11), (5, 33), (119, 3), (21, 17), (7, 51), (13, 17), (23, 33), (47, 17), (7, 33)]:
        test_pair(d0, d1)
    # excluded characters for n = 5 mod 8 with three primes
    for n in (165, 357):
        D = -64*n
        divs = [e for e in range(1, n+1) if n % e == 0]
        S, h = sums(D, -8, divs)
        res = []
        for e in divs:
            P = (S[e] - I*S[n//e])/4
            res.append((e, e % 8, bool(is_torsion(16*P))))
        print("n=%d: (e, e mod 8, P_{chi_e} torsion?) =" % n, res)

if __name__ == "__main__" and "thm36" in sys.argv:
    from mpmath import conj
    for n in (5, 13, 21, 29, 37, 53):
        tau0 = mpc(1, sqrt(mpf(n)))/(4*(n+1))      # root of [16(n+1), -8, 1]
        Z0 = zphi(tau0)
        zm = (1 - I)*Z0     # project's z_n = (1 - [i]) f0(P_n)
        zp = (1 + I)*Z0     # other sign
        print("n=%d: z_n + conj(z_n): project sign coords %s (torsion den %d) | other sign coords %s (torsion den %d)   [tau(1)=(0,0) has coords (0.5,-0.5) mod Z[i]]"
              % (n, show(zm + conj(zm)), is_torsion(zm + conj(zm)), show(zp + conj(zp)), is_torsion(zp + conj(zp))))
