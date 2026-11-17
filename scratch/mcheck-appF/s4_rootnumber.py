"""mcheck-appF s4: the sign bookkeeping behind alpha(-1) = 1 (tex L8588-8600), checked numerically.

Claims used: w(E) = -prod_{p^e || N} w_{p^e};  w(E^{h*}) = w(E) chi_{h*}(-N) for (h*, N) = 1;
hence w(E^{h*}) = prod w_{p^e} chi_{h*}(p)^e, which is +1 when L(E^{h*},1) != 0.
The root number of each curve is computed from its L-series alone, via F(1/t) = w t^2 F(t),
F(t) = sum a_n exp(-2 pi n t / sqrt(N)). At a prime of multiplicative reduction w_p = -a_p.
"""
import math

results = []


def check(name, ok, info=""):
    results.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name + ((" : " + str(info)) if info else ""))


def neg(name, claim_value, info=""):
    check("NEG " + name + " (wrong input must fail)", not claim_value, info)


def leg(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def kron(D, n):
    """Kronecker symbol (D/n) for n > 0, D a discriminant."""
    r = 1
    x = n
    while x % 2 == 0:
        x //= 2
        if D % 2 == 0:
            return 0
        r *= 1 if D % 8 in (1, 7) else -1
    p = 3
    while x > 1 and p * p <= x:
        while x % p == 0:
            r *= leg(D, p)
            x //= p
        p += 2
    if x > 1:
        r *= leg(D, x)
    return r


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def ap(curve, p):
    a1, a2, a3, a4, a6 = curve
    if p == 2:
        cnt = 1
        for x in range(2):
            for y in range(2):
                if (y * y + a1 * x * y + a3 * y - (x**3 + a2 * x * x + a4 * x + a6)) % 2 == 0:
                    cnt += 1
        return p + 1 - cnt
    cnt = 1
    for x in range(p):
        disc = (a1 * x + a3) ** 2 + 4 * (x**3 + a2 * x * x + a4 * x + a6)
        cnt += 1 + leg(disc, p)
    return p + 1 - cnt


def an_list(curve, N, nmax, twist=1):
    ps = primes_upto(nmax)
    apd = {p: ap(curve, p) for p in ps}
    a = [0] * (nmax + 1)
    a[1] = 1
    # multiplicative construction
    for n in range(2, nmax + 1):
        pass
    spf = list(range(nmax + 1))
    for p in ps:
        for k in range(p * p, nmax + 1, p):
            if spf[k] == k:
                spf[k] = p
    for n in range(2, nmax + 1):
        p = spf[n]
        m, e = n, 0
        while m % p == 0:
            m //= p
            e += 1
        # a_{p^e}
        c = kron(twist, p) if twist != 1 else 1
        app = apd[p] * c
        bad = (N % p == 0) or (twist != 1 and twist % p == 0)
        if bad:
            ape = app**e
        else:
            prev2, prev = 1, app
            for _ in range(e - 1):
                prev2, prev = prev, app * prev - p * prev2
            ape = prev if e >= 1 else 1
        a[n] = ape * a[m]
    return a, apd


def root_number(a, Nc):
    def F(t):
        return sum(a[n] * math.exp(-2 * math.pi * n * t / math.sqrt(Nc)) for n in range(1, len(a)))
    ws = []
    for t in (1.1, 1.25):
        ws.append(F(1 / t) / (t * t * F(t)))
    return ws


CURVES = {
    "11a1": ((0, -1, 1, -10, -20), 11),
    "37a1": ((0, 0, 1, -1, 0), 37),
    "15a1": ((1, 1, 1, -10, -10), 15),
    "14a1": ((1, 0, 1, 4, -6), 14),
}
TWISTS = [-7, -11, -19, -23, -31, -35, -39, -43]

ok_all = True
okneg = True
rows = []
for name, (cv, N) in CURVES.items():
    nmax = int(9 * math.sqrt(N)) + 10
    a, apd = an_list(cv, N, nmax)
    wE = root_number(a, N)
    wEr = round(wE[0])
    badp = [p for p in primes_upto(N) if N % p == 0]
    wps = {p: -apd[p] for p in badp}  # all these curves have multiplicative reduction (squarefree N)
    pred_wE = -math.prod(wps.values())
    good = abs(wE[0] - wEr) < 1e-6 and abs(wE[1] - wEr) < 1e-6 and wEr == pred_wE
    ok_all &= good
    rows.append((name, "w(E)", wEr, pred_wE))
    for h in TWISTS:
        if math.gcd(h, N) > 1:
            continue
        Nc = N * h * h
        nmax = int(9 * math.sqrt(Nc)) + 10
        at, _ = an_list(cv, N, nmax, twist=h)
        wt = root_number(at, Nc)
        wtr = round(wt[0])
        chiN = kron(h, N)
        pred1 = wEr * kron(h, 1) * (-1) * chiN  # chi_{h*}(-N) = chi(-1) chi(N), chi(-1) = -1 since h* < 0
        pred2 = math.prod(wps[p] * kron(h, p) for p in badp)  # prod w_{p^e} chi(p)^e (e = 1 here)
        g = abs(wt[0] - wtr) < 1e-5 and abs(wt[1] - wtr) < 1e-5 and wtr == pred1 == pred2
        ok_all &= g
        if wtr != wEr * chiN:
            okneg = False
        rows.append((name, h, wtr, pred1, pred2))
check("L8592-8599 w(E) = -prod w_p and w(E^{h*}) = w(E) chi_{h*}(-N) = prod w_{p^e} chi_{h*}(p)^e (4 curves x 8 twists)", ok_all, rows[:6])
neg("w(E^{h*}) = w(E) chi_{h*}(N) (sign chi(-1) dropped)", okneg)

npass = sum(ok for _, ok in results)
print("\n%d/%d PASS" % (npass, len(results)))
for r in rows:
    print(r)
