"""tyz-lcal numerical audit of the three L-leaves (pure Python 3, no PARI on this host).

For squarefree m = 1, 3 (mod 8):
  * L(C_m, 1) by the rapidly convergent series L(E,1) = 2 sum_n a_n/n exp(-2 pi n / sqrt N),
    N = 32 m^2 (conductor of C_m, m odd squarefree), root number +1 for m = 1, 3 (mod 8);
    a_n multiplicative, a_p(C_m) = (m/p) a_p(C_1) for odd p not dividing m, a_p = 0 for p | 2m,
    a_{p^{k+2}} = a_p a_{p^{k+1}} - p a_{p^k};
  * omegaInt = int_1^oo dx / sqrt(x^3 - x), by quadrature and by pi / AGM(1, sqrt 2);
  * lcalSq(m) = L(C_m,1) / (2^{2k-3} * (2/sqrt m) * omegaInt), k = number of prime factors;
  * g(m) = #2Cl(Q(sqrt -m)) = h / 2^{t-1} (genus theory), h by counting reduced forms;
  * LemmaTwoEight for ell(m) = round(sqrt(lcalSq m)) (the sign is irrelevant mod 2);
  * Tunnell cross-check: a_T(m) = coefficient of q^m in eta(8z) eta(16z) theta(2z); test |ell(m)| = |a_T(m)| / 2^k.
Sample: the first 30 squarefree m = 1, 3 (mod 8).
"""
import math

def factor(n):
    f, p = [], 2
    while p * p <= n:
        while n % p == 0:
            f.append(p); n //= p
        p += 1
    if n > 1: f.append(n)
    return f

def squarefree(n):
    f = factor(n); return len(f) == len(set(f))

def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]

AP1 = {}
def ap_C1(p):
    if p in AP1: return AP1[p]
    if p == 2: v = 0
    elif p % 4 == 3: v = 0
    else:
        sq = [0] * p
        for y in range(p): sq[y * y % p] += 1
        cnt = sum(sq[(x * x * x - x) % p] for x in range(p))
        v = p - cnt
    AP1[p] = v; return v

def coeffs(m, nmax):
    a = [0] * (nmax + 1); a[1] = 1
    spf = list(range(nmax + 1))
    for i in range(2, int(nmax ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, nmax + 1, i):
                if spf[j] == j: spf[j] = i
    for n in range(2, nmax + 1):
        p = spf[n]; k = 0; q = n
        while q % p == 0: q //= p; k += 1
        if q > 1:
            a[n] = a[q] * a[n // q]; continue
        # n = p^k
        if p == 2 or m % p == 0: a[n] = 0; continue
        ap = legendre(m, p) * ap_C1(p)
        if k == 1: a[n] = ap
        else: a[n] = ap * a[n // p] - p * a[n // (p * p)]
    return a

def L1(m):
    N = 32 * m * m; c = 2 * math.pi / math.sqrt(N)
    nmax = int(40 / c) + 10
    a = coeffs(m, nmax)
    return 2 * sum(a[n] / n * math.exp(-c * n) for n in range(1, nmax + 1))

def agm(a, b):
    for _ in range(60): a, b = (a + b) / 2, math.sqrt(a * b)
    return a

def omega_quad():
    # x = 1 + u^2 on [1, 2]:  dx/sqrt(x^3-x) = 2 du / sqrt((1+u^2)(2+u^2));  x = 1/t^2 on [2, oo).
    def simpson(f, a, b, n=20000):
        h = (b - a) / n; s = f(a) + f(b)
        for i in range(1, n): s += (4 if i % 2 else 2) * f(a + i * h)
        return s * h / 3
    I1 = simpson(lambda u: 2 / math.sqrt((1 + u * u) * (2 + u * u)), 0, 1)
    # x = 1/t^2, dx = -2 t^-3 dt, sqrt(x^3-x) = t^-3 sqrt(1 - t^4): integrand 2/sqrt(1-t^4), t in (0, 1/sqrt2]
    I2 = simpson(lambda t: 2 / math.sqrt(1 - t ** 4), 0, 1 / math.sqrt(2))
    return I1 + I2

def classno(D):  # D < 0 fundamental discriminant: number of reduced primitive forms
    h = 0; a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a): continue
            c = (b * b - D) // (4 * a)
            if c < a: continue
            if b < 0 and a == c: continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1: continue
            h += 1
        a += 1
    return h

def gval(m):
    D = -m if m % 4 == 3 else -4 * m
    t = len(set(factor(-D)))
    h = classno(D)
    assert h % (2 ** (t - 1)) == 0
    return h // 2 ** (t - 1)

def tunnell(nmax):
    # eta(8z) eta(16z) theta(2z) = q prod (1-q^{8n})(1-q^{16n}) * sum_y q^{2y^2}
    P = [0] * (nmax + 1); P[0] = 1
    for step in (8, 16):
        for n in range(1, nmax // step + 1):
            e = step * n
            for i in range(nmax, e - 1, -1): P[i] -= P[i - e]
    T = [0] * (nmax + 1)
    y = 0
    while 2 * y * y <= nmax:
        for i in range(nmax + 1 - 2 * y * y):
            T[i + 2 * y * y] += P[i] * (1 if y == 0 else 2)
        y += 1
    return [0] + T[:nmax]  # shift by q

if __name__ == '__main__':
    om_q, om_a = omega_quad(), math.pi / agm(1, math.sqrt(2))
    print(f"omegaInt: quadrature {om_q:.12f}, pi/AGM(1,sqrt2) {om_a:.12f}")
    ms = [m for m in range(1, 400) if m % 8 in (1, 3) and squarefree(m)][:30]
    TT = tunnell(max(ms) + 1)
    ell = {}
    for m in ms:
        k = len(factor(m)) if m > 1 else 0
        v = L1(m) / (2.0 ** (2 * k - 3) * (2 / math.sqrt(m)) * om_a)
        r = round(math.sqrt(max(v, 0)))
        ell[m] = r
        print(f"m={m:4d} k={k} L(C_m,1)={L1(m):.10f} lcalSq={v:.8f} ell=+-{r} sqErr={abs(v-r*r):.1e}"
              f" g={gval(m)} tunnell a(m)={TT[m]} |a|/2^k={abs(TT[m])/2**k}")
    # LemmaTwoEight mod 2
    ok = True
    for m in ms:
        if m == 1: continue
        if m % 8 == 1:
            s = sum(ell[d] * ell[m // d] for d in range(1, m + 1) if m % d == 0 and d % 8 == 1 and d * d < m)
        else:
            s = sum(ell[m // d] * ell[d] for d in range(1, m + 1) if m % d == 0 and d % 8 == 1)
        good = (s - gval(m)) % 2 == 0
        ok &= good
        print(f"LemmaTwoEight m={m}: sum={s} g={gval(m)} {'ok' if good else 'FAIL'}")
    print("LemmaTwoEight all ok:", ok)
