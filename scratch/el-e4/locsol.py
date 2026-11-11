"""p-adic local solubility of y^2 = f(x), f in Q[x] of even degree (quartic), exact integer arithmetic.
locsol(f, p) -> True / False / None(undecided at depth limit). f: list of Fractions, f[i] = coeff of x^i."""
from fractions import Fraction as Fr
from math import gcd

def val(n, p):
    if n == 0: return 10**9
    v = 0
    while n % p == 0: n //= p; v += 1
    return v

def is_sq_unit(u, p, prec):
    # u a p-adic unit known mod p^prec; return True/False/None
    if p == 2:
        if prec < 3: return None
        return u % 8 == 1
    return pow(u % p, (p - 1) // 2, p) == 1

def to_int(f):
    # scale by an even power-square so all coeffs are integers (square class preserved)
    L = 1
    for c in f: L = L * Fr(c).denominator // gcd(L, Fr(c).denominator)
    return [int(Fr(c) * L * L) for c in f]

def subst(g, t0, p):
    # g(t0 + p t) coefficients (binomial expansion)
    n = len(g); h = [0] * n
    from math import comb
    for i, c in enumerate(g):
        if c == 0: continue
        for k in range(i + 1):
            h[k] += c * comb(i, k) * t0 ** (i - k) * p ** k
    return h

def zp_sol(g, p, depth):
    # exists t in Zp with g(t) in Qp*^2 (or g(t)=0)?
    if all(c == 0 for c in g): return True
    m = min(val(c, p) for c in g if c)
    if m >= 2:
        e = m // 2 * 2; g = [c // p ** e for c in g]
    if depth == 0: return None
    undecided = False
    for t0 in range(p):
        h = subst(g, t0, p)
        v0 = val(h[0], p)
        v1 = min([val(c, p) for c in h[1:] if c] or [10**9])
        if h[0] == 0 and all(c == 0 for c in h[1:]): return True
        if v0 < v1:
            prec = v1 - v0
            if v0 % 2 == 1: continue          # odd valuation on the whole disc
            u = h[0] // p ** v0
            s = is_sq_unit(u, p, prec)
            if s is True: return True
            if s is False: continue
        r = zp_sol(h, p, depth - 1)
        if r is True: return True
        if r is None: undecided = True
    return None if undecided else False

def locsol(f, p, depth=40):
    g = to_int(f)
    r1 = zp_sol(g, p, depth)
    if r1 is True: return True
    # x = 1/(p u), u in Zp: y^2 = f(1/x) x^deg ; points with |x|>1
    d = len(g) - 1
    grev = list(reversed(g))           # grev(s) = s^d f(1/s)
    gs = [c * p ** i for i, c in enumerate(grev)]  # s = p u
    r2 = zp_sol(gs, p, depth)
    if r2 is True: return True
    return None if (r1 is None or r2 is None) else False

def quartic(m, Th, R0):
    # m(m Th^2 - R0 (1 - R0 q^2)^2) as coefficients in q
    m, Th, R0 = Fr(m), Fr(Th), Fr(R0)
    return [m * (m * Th * Th - R0), Fr(0), 2 * m * R0 * R0, Fr(0), -m * R0 ** 3]
