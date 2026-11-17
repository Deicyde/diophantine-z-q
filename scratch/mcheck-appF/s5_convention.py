"""mcheck-appF s5: the classical character attached to local scaling characters (tex L8909-8933, L8990-9015).

The tex claims: if the finite Schwartz function satisfies f(vx) = alpha(v) f(x), the classical
character of the theta series, relative to the ordinary theta multiplier, is
  prod_p alpha_p(d) * prod_p (d, det Q)_p   at gamma = [[a,b],[c,d]],  "not its inverse",
and for a scaled form Q/m with det squareclass m the extra factor is (m/d) (O.5c).
Here this is tested numerically in rank one, where the same adelic-to-classical passage applies:
  theta_chi(tau) = sum_n chi(n) e(n^2 tau), chi an even character of order 4 mod 17 (alpha_17 = chi),
  theta(m tau)  for m = 7, 11, 19 (det squareclass m),
by evaluating  [theta_f(g tau)/theta_f(tau)] / [theta(g tau)/theta(tau)]  for g in Gamma_0(4 * 17^2) etc.
The answer chi(d) (not conj(chi(d))) distinguishes the convention; a negative control uses the inverse.
"""
import cmath
import math

results = []


def check(name, ok, info=""):
    results.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name + ((" : " + str(info)) if info else ""))


def neg(name, claim_value, info=""):
    check("NEG " + name + " (wrong input must fail)", not claim_value, info)


def jacobi(a, n):
    a %= n
    r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            r = -r
        a %= n
    return r if n == 1 else 0


P = 17
G = 3  # primitive root mod 17
dlog = {pow(G, k, P): k for k in range(P - 1)}


def chi(n):
    n %= P
    if n == 0:
        return 0
    return 1j ** (dlog[n] % 4)


assert abs(chi(P - 1) - 1) < 1e-12  # even


def theta_w(tau, w, scale=1, nmax=200):
    return sum(w(n) * cmath.exp(2j * math.pi * n * n * scale * tau) for n in range(-nmax, nmax + 1))


def ratio(weight, scale, a, b, c, d, y0=1.0):
    tau = complex(-d / c, y0 / c)
    gt = (a * tau + b) / (c * tau + d)
    one = lambda n: 1
    num = theta_w(gt, weight, scale) / theta_w(tau, weight, scale)
    den = theta_w(gt, one) / theta_w(tau, one)
    return num / den


def gamma_with(c, d):
    a = pow(d, -1, c)
    b = (a * d - 1) // c
    return a, b, c, d


ok = True
okneg = True
vals = []
c = 4 * P * P
for d in (3, 5, 7, 11, 13, 23, 29, 31, 37, 39):
    if math.gcd(d, c) > 1:
        continue
    a, b, c_, d_ = gamma_with(c, d)
    r = ratio(chi, 1, a, b, c_, d_)
    vals.append((d, complex(round(r.real, 6), round(r.imag, 6)), chi(d)))
    ok &= abs(r - chi(d)) < 1e-6
    if abs(r - chi(d).conjugate()) > 1e-6:
        okneg = False
check("L8913-8933/L8990-9015 classical character = prod alpha_p(d) (order-4 alpha_17), not its inverse", ok, vals[:4])
neg("classical character = conj(prod alpha_p(d))", okneg)

ok = True
okneg = True
for m in (7, 11, 19, 3 * 7):
    c = 4 * m
    for d in (1, 5, 9, 13, 17, 25, 29, 37, 41, 53):
        if math.gcd(d, c) > 1:
            continue
        a, b, c_, d_ = gamma_with(c, d)
        r = ratio(lambda n: 1, m, a, b, c_, d_)
        ok &= abs(r - jacobi(m, d)) < 1e-6
        if abs(r - 1) > 1e-6:
            okneg = False
check("(O.5c) extraction: theta(m tau) has relative character (m/d) (m = 7, 11, 19, 21)", ok)
neg("extraction adds no character", okneg)

npass = sum(ok for _, ok in results)
print("\n%d/%d PASS" % (npass, len(results)))
