"""Independent check of Lemma P (nt-22p.md, section 3.2) at the primes of S0.

Part A: 2-adic square class of R0 (eta = 1) for poles of order e = 1..6 at 2, exhaustive mod 2^(e+6).
Part B: 30 random slopes t = u/v with poles at all five primes of S0 (e_l >= 1, e_2 >= 3),
        F(t) > 0; build one rational q by CRT with v_l(1 - R0 q^2) >= N_l at all five primes,
        then compute the pole input B = R/Theta^2 exactly in Q(sqrt2) with random test values
        D_gj in Z[sqrt2] (integral above every prime) and ell0 = 1 (worst case E_l = 0).
Part C: negative control, alpha = v_l(a) chosen below 23 e: does v_l(B) >= 4 fail?
"""
from fractions import Fraction as Fr
import random, sys

CSET = [0, -15, -20, -24, -30, -60]
S0 = [2, 3, 5, 7, 13]
K = [1] * 8 + [25] * 4


def vp(x, p):
    """p-adic valuation of a nonzero rational (Fraction or int)."""
    x = Fr(x)
    assert x != 0
    n, d, v = x.numerator, x.denominator, 0
    while n % p == 0:
        n //= p; v += 1
    while d % p == 0:
        d //= p; v -= 1
    return v


def v12(p):
    return vp(12, p)


# ---------- K0 = Q(sqrt2) arithmetic: pairs (a, b) = a + b sqrt2 ----------
def kmul(x, y):
    return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def kadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def kinv(x):
    n = x[0] * x[0] - 2 * x[1] * x[1]
    return (x[0] / n, -x[1] / n)


def kscal(r, x):
    return (r * x[0], r * x[1])


# ---------- Part A ----------
def partA():
    out = {}
    for e in range(1, 7):
        mod = 2 ** (e + 6)
        classes = set()
        for u in range(1, mod, 2):
            for w in range(1, 2 ** 6, 2):
                v = (2 ** e) * w
                P = 1
                for c in CSET:
                    P *= (u - c * v)
                # R0 * 2^(-2e) = w^2 * P / (u - v)^8 ; w, u - v odd -> square class of P mod 8
                classes.add(P % 8)
        out[e] = sorted(classes)
    return out


# ---------- square roots mod l^M ----------
def sqrt_mod_prime_power(a, p, M):
    """Some x with x^2 = a mod p^M, a a unit (and a = 1 mod 8 if p = 2)."""
    if p == 2:
        assert a % 8 == 1
        x = 1
        for k in range(3, M):  # x^2 = a mod 2^k  ->  mod 2^(k+1)
            if (x * x - a) % (2 ** (k + 1)) != 0:
                x += 2 ** (k - 1)
        assert (x * x - a) % (2 ** M) == 0
        return x
    # odd p: brute root mod p, then Hensel
    r = next(r for r in range(1, p) if (r * r - a) % p == 0)
    pk = p
    for _ in range(1, M):
        pk2 = pk * p
        # r <- r - (r^2 - a)/(2r) mod pk2
        r = (r - (r * r - a) * pow(2 * r, -1, pk2)) % pk2
        pk = pk2
    assert (r * r - a) % (p ** M) == 0
    return r


def crt(res):
    """res: list of (residue, modulus) with coprime moduli."""
    x, m = 0, 1
    for r, n in res:
        t = ((r - x) * pow(m, -1, n)) % n
        x += m * t
        m *= n
    return x % m, m


def contactF(t):
    P = Fr(1)
    for c in CSET:
        P *= (t - c)
    return P


def pole_input(t, q, D, ell=1):
    R0 = contactF(t) / (t - 1) ** 8
    a = 1 - R0 * q * q
    R = Fr(ell) ** 2 * a * a * R0
    W = []
    for g in range(6):
        Wg = (Fr(1), Fr(0))
        for j in range(12):
            den = R0 ** K[j] * (t - 1) ** (K[j] + 1)
            C = kscal(1 / den, D[g][j])
            Wg = kmul(Wg, kadd((Fr(1), Fr(0)), kscal(R, kmul(C, C))))
        W.append(Wg)
    S = (Fr(0), Fr(0))
    for Wg in W:
        S = kadd(S, kinv(Wg))
    Theta = 2 * S[0]
    return R0, a, R, Theta, R / Theta ** 2


def build_q(t, u, v, N, shift=None):
    """q = m / prod l^e_l with v_l(1 - R0 q^2) >= N_l at each l in S0.
    shift: optional dict l -> exponent to perturb q (negative control)."""
    R0 = contactF(t) / (t - 1) ** 8
    es = {l: vp(v, l) for l in S0}
    L = 1
    for l in S0:
        L *= l ** es[l]
    res = []
    for l in S0:
        e = es[l]
        unit = R0 / Fr(l) ** (2 * e)          # l-adic unit, a square
        M = N[l] + 4
        mod = l ** M
        un = unit.numerator % mod * pow(unit.denominator, -1, mod) % mod
        w = sqrt_mod_prime_power(pow(un, -1, mod), l, M)   # w^2 * unit = 1 mod l^M
        if shift and l in shift:
            w = w + l ** shift[l]
        # q = m / L must have q * l^e = w, i.e. m * (l^e / L) = w mod l^M
        cof = L // l ** e
        res.append((w * pow(cof, -1, mod) % mod, mod))
    m, mod = crt(res)
    return Fr(m, L), es


def partB(nsamp=30, seed=1, control=False):
    rng = random.Random(seed)
    rows = []
    for s in range(nsamp):
        es = {2: rng.randint(3, 8)}
        for l in S0[1:]:
            es[l] = rng.randint(1, 5)
        v = 1
        for l in S0:
            v *= l ** es[l]
        while True:
            u = rng.randint(1, 10 ** 6) * rng.choice([1, -1])
            from math import gcd
            if gcd(u, v) != 1:
                continue
            t = Fr(u, v)
            if contactF(t) > 0:
                break
        N = {l: 23 * es[l] + v12(l) + 2 for l in S0}
        shift = None
        if control:
            # alpha about 20 e (< 23 e): perturb the root at level 20e - e  (v(a) ~ e + v(2) + level)
            shift = {l: 20 * es[l] - es[l] - (1 if l == 2 else 0) for l in S0}
        q, _ = build_q(t, u, v, N, shift)
        D = [[(Fr(rng.randint(-50, 50) or 1), Fr(rng.randint(-50, 50))) for j in range(12)]
             for g in range(6)]
        R0, a, R, Theta, B = pole_input(t, q, D)
        row = {"e": es, "alpha": {l: vp(a, l) for l in S0},
               "vTheta": {l: vp(Theta, l) for l in S0},
               "vB": {l: vp(B, l) for l in S0},
               "R0sq": all(vp(R0, l) == 2 * es[l] for l in S0)}
        rows.append(row)
    return rows


if __name__ == "__main__":
    print("Part A: square classes mod 8 of prod(u - c v) for v_2(v) = e:")
    for e, cl in partA().items():
        print("  e =", e, "classes", cl, "(square iff class == [1])")
    for label, control in (("B", False), ("C (control, alpha ~ 20e)", True)):
        rows = partB(30, seed=7 if control else 1, control=control)
        ok_theta = sum(all(r["vTheta"][l] == v12(l) for l in S0) for r in rows)
        ok_B = sum(all(r["vB"][l] >= 4 for l in S0) for r in rows)
        ok_N = sum(all(r["alpha"][l] >= 23 * r["e"][l] + v12(l) + 2 for l in S0) for r in rows)
        ok_formula = sum(all(r["vB"][l] == 2 * r["alpha"][l] + 2 * r["e"][l] - 2 * v12(l)
                             for l in S0 if r["vTheta"][l] == v12(l)) for r in rows)
        print(f"Part {label}: samples {len(rows)}; alpha >= N at all l: {ok_N}; "
              f"v(Theta)=v(12) at all l: {ok_theta}; v(B)>=4 at all l: {ok_B}; "
              f"v(B)=2alpha+2e-2v(12) where v(Theta)=v(12): {ok_formula}")
        if control:
            for r in rows[:5]:
                print("   ", r)
        else:
            print("    min over samples/primes of v(B) - (46e+4):",
                  min(r["vB"][l] - (46 * r["e"][l] + 4) for r in rows for l in S0))
