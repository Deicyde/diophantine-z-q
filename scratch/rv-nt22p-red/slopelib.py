"""Independent implementation of the slope predicate data (manuscript lines 1177-1191,
completeness lines 1720-1758; Lean `poleInput`, `slope_complete`, `weak_approx_q`) and of the
modified choice of q (nt-22p section 3.2).  Written from the definitions, not from scratch/nt-22p.

Model of the old primes: S_b = S_ht ∪ H, where S_ht = primes <= 324 and H is a finite list of
primes > 324 standing in for the catalogue (B_p = 1).  ell0 = 12 * prod_{S_ht} p^2916 *
prod_H p^732, which has the valuations E_p of the manuscript at every prime of the model.

The pole input B = R / Theta^2 is never formed as a rational (it would have millions of digits);
its valuation at a prime p is computed p-adically (PARI p-adics, with precision tracking) from
exact rationals t, q, a, R0 and exact ell0, and its real value with mpmath.
"""
from fractions import Fraction as Fr
import math, random, sys
sys.set_int_max_str_digits(0)
import gmpy2
from gmpy2 import mpz
import cypari2
import mpmath

pari = cypari2.Pari()
pari.allocatemem(4 * 10**9, silent=True)
mpmath.mp.dps = 60

CSET = [0, -15, -20, -24, -30, -60]
S_HT = [int(p) for p in pari('primes([2,324])')]
S0 = [2, 3, 5, 7, 13]


def vp_int(n, p):
    n = mpz(n)
    if n == 0:
        return 10**9
    return int(gmpy2.remove(n, p)[1])


def vp(x, p):
    x = Fr(x)
    if x == 0:
        return 10**9
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


def Bp(p):
    return 4 if p <= 324 else 1


def Cp(p):
    return 14 * Bp(p)


def Ep(p):
    return 52 * Cp(p) + vp_int(12, p) + 4


def F(t):
    r = Fr(1)
    for c in CSET:
        r *= (t - c)
    return r


def R0_of(t, eta):
    return eta * F(t) / (t - 1) ** 8


def ell0(H):
    r = mpz(12)
    for p in S_HT:
        r *= mpz(p) ** 2916
    for p in H:
        r *= mpz(p) ** 732
    return r


def field2_holds(t, p):
    """Field 2 (`GoodSlope.old`) at p."""
    return abs(vp(t - 1, p)) <= Bp(p) and abs(vp(F(t) / (t - 1) ** 8, p)) <= 8 * Bp(p)


def lemmaP_hyp(t, l):
    """Hypotheses of Lemma P at l: l^e || den(t), e >= 1, the seven numerators prime to l,
    F(t) > 0, and (l odd or e >= 3)."""
    u, v = t.numerator, t.denominator
    e = vp_int(v, l)
    if e < 1 or F(t) <= 0:
        return False
    if any((u - c * v) % l == 0 for c in CSET + [1]):
        return False
    return l != 2 or e >= 3


def padic(x, p, M):
    """Exact rational x as a PARI p-adic with relative precision M."""
    x = Fr(x)
    if x == 0:
        return pari(f"O({p}^{M})")
    n, d = mpz(x.numerator), mpz(x.denominator)
    n1, a = gmpy2.remove(n, p)
    d1, b = gmpy2.remove(d, p)
    mod = mpz(p) ** M
    unit = (n1 % mod) * gmpy2.invert(d1 % mod, mod) % mod
    return pari(f"({int(unit)} + O({p}^{M})) * {p}^({int(a) - int(b)})")


def padic_bigint_unitpart(n, p, M):
    n1, a = gmpy2.remove(mpz(n), p)
    mod = mpz(p) ** M
    return int(n1 % mod), int(a)


def unit_sqrt_mod(U, l, K):
    """An integer w with U w^2 == 1 mod l^K (U an l-adic unit given as a Fraction), or None."""
    x = padic(1 / Fr(U), l, K + 5)
    if not int(pari.issquare(x)):
        return None
    s = pari.sqrt(x)
    w = int(pari.truncate(s)) if int(pari.valuation(s, l)) >= 0 else None
    return w % (l ** K)


def is_square_Ql(x, l):
    return bool(int(pari.issquare(padic(x, l, 40))))


# ---------------------------------------------------------------------------
# The witness q (weak approximation, nt-22p section 3.2)
# ---------------------------------------------------------------------------

def choose_q(t, eta, Sb, Spole, Nl, sel, avoid, ell0_val, Cmax_log10=0.0, slack=40,
             rng=None, sign=1):
    """A rational q = m / (Dpole * Laux^k) with
      * l in Spole: v_l(1 - R0 q^2) >= Nl[l]  (q in the ball of Lemma P(2));
      * p in Sb \\ Spole: v_p(q) >= C_p      (the old choice);
      * p in sel: v_p(q) >= 0;
      * |q - R0^{-1/2}| so small that R C^2 < 10^-slack for |C| <= 10^Cmax_log10.
    Returns (q, info)."""
    R0 = R0_of(t, eta)
    assert R0 > 0
    Dpole = 1
    targets = {}          # l -> (w, e): q0 = w / l^e
    for l in Spole:
        r = vp(R0, l)
        assert r % 2 == 0, (l, r)
        e = r // 2
        U = R0 / Fr(l) ** r
        K = Nl[l] + 2
        w = unit_sqrt_mod(U, l, K + e + 2)
        if w is None:
            raise ValueError(f"R0 not a square in Q_{l}")
        targets[l] = (w, e, K)
        Dpole *= l ** e
    # auxiliary prime outside everything
    bad = set(Sb) | set(sel) | set(avoid)
    Laux = 10**6 + 3
    while Laux in bad or not gmpy2.is_prime(Laux):
        Laux += 2
    # residue conditions on m modulo Mres
    mods = []
    for l in Spole:
        w, e, K = targets[l]
        mod = mpz(l) ** (K + e)
        mods.append((mod, None, l))
    for p in Sb:
        if p not in Spole:
            mods.append((mpz(p) ** Cp(p), 0, p))
    Mres = mpz(1)
    for mod, _, _ in mods:
        Mres *= mod
    # size of Laux^k: R = ell0^2 a^2 R0 with |a| <~ 2 sqrt(R0) Mres / (Dpole Laux^k)
    log_ell0 = gmpy2.num_digits(mpz(ell0_val), 10)
    log_need = (log_ell0 + gmpy2.num_digits(Mres, 10) + Cmax_log10 + slack
                + 1.5 * abs(math.log10(float(R0))) + 5)
    k = int(log_need / math.log10(Laux)) + 2
    Lk = mpz(Laux) ** k
    Den = mpz(Dpole) * Lk
    # residues: q0 * Den = w * (Dpole / l^e) * Lk  (mod l^(K+e))
    res = []
    for mod, r, l in mods:
        if r is None:
            w, e, K = targets[l]
            r = (sign * w * (Dpole // l ** e) * Lk) % mod
        res.append((mod, r))
    # CRT
    m0, M = mpz(0), mpz(1)
    for mod, r in res:
        # solve m == m0 mod M, m == r mod mod
        inv = gmpy2.invert(M % mod, mod)
        m0 = m0 + M * (((r - m0) % mod) * inv % mod)
        M *= mod
        m0 %= M
    # target real value x0 * Den with x0 = R0^{-1/2}: integer sqrt of Den^2 / R0
    X = gmpy2.isqrt(Den * Den * R0.denominator // R0.numerator)
    m = X - ((X - m0) % M)
    if sign < 0:
        pass
    q = Fr(int(m), int(Den))
    if q * q * R0 == 1:
        m += M
        q = Fr(int(m), int(Den))
    info = dict(Laux=Laux, k=k, Dpole=Dpole, Mres_digits=int(gmpy2.num_digits(M, 10)))
    return q, info


# ---------------------------------------------------------------------------
# Test values (model) and the pole input
# ---------------------------------------------------------------------------

def prime_above(p):
    """(x, y) with x^2 - 2 y^2 = +-p, i.e. a generator of a prime of Z[sqrt2] above split p."""
    for y in range(1, 10**6):
        for s in (1, -1):
            x2 = s * p + 2 * y * y
            if x2 > 0:
                x = gmpy2.isqrt(x2)
                if x * x == x2:
                    return (int(x), y)
    raise ValueError


def zmul(a, b):
    return (a[0] * b[0] + 2 * a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def zpow(a, k):
    r = (1, 0)
    for _ in range(k):
        r = zmul(r, a)
    return r


PREC = [1] * 8 + [25] * 4


def model_tests(sel_primes, rng, mode="random", ngroups=6):
    """D[g][j] in Z[sqrt2].  Group i < len(sel_primes) is assigned to sel_primes[i]: its tests are
    divisible by pi^{k_j} for a prime pi above it.  mode 'random': random small cofactors;
    'one': cofactor 1 (tests exactly pi^{k_j}, unassigned groups D = 1)."""
    D = []
    for g in range(ngroups):
        row = []
        for j in range(12):
            if mode == "one":
                cof = (1, 0)
            else:
                cof = (rng.randint(-10**6, 10**6), rng.randint(-10**6, 10**6))
            if g < len(sel_primes):
                pi = prime_above(sel_primes[g])
                row.append(zmul(zpow(pi, PREC[j]), cof))
            else:
                row.append(cof)
        D.append(row)
    return D


class PoleInput:
    """Local and real data of B = R / Theta^2 for slope t, sign eta, witness q, ell0, tests D."""

    def __init__(self, t, eta, q, ell0_val, D):
        self.t, self.eta, self.q, self.ell0, self.D = Fr(t), eta, Fr(q), mpz(ell0_val), D
        self.R0 = R0_of(self.t, eta)
        q2 = self.q * self.q
        # a = 1 - R0 q^2 exactly, as numerator/denominator big ints
        n = mpz(self.R0.denominator) * mpz(self.q.denominator) ** 2 - \
            mpz(self.R0.numerator) * mpz(self.q.numerator) ** 2
        d = mpz(self.R0.denominator) * mpz(self.q.denominator) ** 2
        g = gmpy2.gcd(n, d)
        self.a_num, self.a_den = n // g, d // g
        assert self.a_num != 0

    def v_a(self, p):
        return vp_int(self.a_num, p) - vp_int(self.a_den, p)

    def local(self, p, M=80):
        """Returns dict with v_p(R), v_p(Theta), v_p(B), precision flag."""
        t, R0 = self.t, self.R0
        # R as p-adic: ell0^2 a^2 R0
        lu, lv = padic_bigint_unitpart(self.ell0, p, M)
        nu, nv = padic_bigint_unitpart(self.a_num, p, M)
        du, dv = padic_bigint_unitpart(self.a_den, p, M)
        mod = p ** M
        a_unit = nu * pow(du, -1, mod) % mod
        Rp = pari(f"({lu}+O({p}^{M}))^2 * {p}^({2*lv})") * \
            pari(f"({a_unit}+O({p}^{M}))^2 * {p}^({2*(nv-dv)})") * padic(R0, p, M)
        vR = int(pari.valuation(Rp, p))
        Theta = pari(0)
        minW = None
        for g, row in enumerate(self.D):
            W = (pari(1), pari(0))
            for j, (x, y) in enumerate(row):
                k = PREC[j]
                c = padic(1 / (R0 ** k * (t - 1) ** (k + 1)), p, M)
                Cx, Cy = c * x, c * y
                C2 = (Cx * Cx + 2 * Cy * Cy, 2 * Cx * Cy)
                fac = (1 + Rp * C2[0], Rp * C2[1])
                W = (W[0] * fac[0] + 2 * W[1] * fac[1], W[0] * fac[1] + W[1] * fac[0])
            N = W[0] * W[0] - 2 * W[1] * W[1]
            Winv_x = W[0] / N
            Theta = Theta + 2 * Winv_x
        if str(pari.type(Theta)) == 't_PADIC' and int(pari.padicprec(Theta, p)) <= int(pari.valuation(Theta, p)):
            return dict(vR=vR, vTheta=None, vB=None, ok=False)
        vT = int(pari.valuation(Theta, p))
        return dict(vR=vR, vTheta=vT, vB=vR - 2 * vT, ok=True,
                    prec=int(pari.padicprec(Theta, p)) - vT if str(pari.type(Theta)) == 't_PADIC' else 10**9)

    def real(self):
        """B in R (mpmath), and min over embeddings of W_g, Theta."""
        mp = mpmath.mp
        s2 = mpmath.sqrt(2)
        a = mpmath.mpf(int(self.a_num)) / mpmath.mpf(int(self.a_den))
        R = mpmath.mpf(int(self.ell0)) ** 2 * a ** 2 * mpmath.mpf(self.R0.numerator) / self.R0.denominator
        t, R0 = self.t, self.R0
        Theta = mpmath.mpf(0)
        Ws = []
        for sgn in (1, -1):
            for row in self.D:
                W = mpmath.mpf(1)
                for j, (x, y) in enumerate(row):
                    k = PREC[j]
                    den = mpmath.mpf(Fr(R0) ** k * (t - 1) ** (k + 1)) if False else \
                        mpmath.mpf((R0 ** k * (t - 1) ** (k + 1)).numerator) / (R0 ** k * (t - 1) ** (k + 1)).denominator
                    C = (x + sgn * y * s2) / den
                    W *= 1 + R * C * C
                Ws.append(W)
                Theta += 1 / W
        B = R / Theta ** 2
        return dict(R=R, Theta=Theta, B=B, minW=min(Ws))
