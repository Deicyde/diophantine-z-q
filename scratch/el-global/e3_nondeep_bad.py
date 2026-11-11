"""E3: data that is honest except for a non-deep kappa is bad.
Data: t = n (integer), kappa' = 1, h = 2, s0 = 2n, eta = sign F(n), q = 0 (column property: q irrelevant).
For every prime p > 324 with v_p(F(n)) odd, compute v_p(B), B = R/Theta^2 exactly (SixLocalTests.lean).
Claim: v_p(B) is negative and odd. Inputs: n = 1..40 (each prime p counted once per n), capped at 30 cases."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from e1_slice_pole import K, P0, mul, w, z, contacts
from sympy import factorint

def vp(x, p):
    x = Fr(x)
    if x == 0: return None
    v, a, b = 0, x.numerator, x.denominator
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v

def B_of(n, kap, t, q=Fr(0)):
    h, s0 = 2*kap, 2*kap*n
    Ph, Ps, Phk, Psk = mul(h, P0), mul(s0, P0), mul(h - kap, P0), mul(s0 - kap*n, P0)
    F = Fr(1)
    for c in contacts: F *= (Fr(t) - c)
    eta = 1 if F > 0 else -1
    D = [w(Ph), w(Ps), w(Phk).conj(), w(Psk).conj(),
         z(Ps)/z(Ph) - t, (z(Psk)/z(Phk)).conj() - t]
    R0 = eta * 2730**6 * F
    R = R0 * (1 - R0*q*q)**2
    W = K(1)
    for Dj in D:
        C = Dj / K(F)
        W = W * (K(1) + K(R)*C*C)
    Th = 2 * W.inv().a
    return R / (Th*Th), F

if __name__ == "__main__":
    rows = []
    for n in range(1, 41):
        F = 1
        for c in contacts: F *= (n - c)
        ps = [p for p, e in factorint(abs(F)).items() if p > 324 and e % 2 == 1]
        if not ps: continue
        B, _ = B_of(n, 1, n)
        for p in ps:
            rows.append((n, p, vp(F, p), vp(B, p)))
        if len(rows) >= 30: break
    rows = rows[:30]
    for r in rows: print("n=%3d p=%6d v_p(F)=%d v_p(B)=%d" % r)
    print("cases:", len(rows), " all negative odd:", all(v < 0 and v % 2 for *_, v in rows))
