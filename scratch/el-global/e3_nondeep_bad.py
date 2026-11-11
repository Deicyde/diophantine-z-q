"""E3: data that is honest except for a non-deep kappa is bad.
Data: t = n (integer), kappa' = 1, h = 2, s0 = 2n, eta = sign F(n), q = 0 (column property: q irrelevant).
For primes p > 324 with v_p(F(n)) odd, compute v_p(B), B = R/Theta^2 (SixLocalTests.lean), p-adically:
K0 (x) Q_p as Mod(a + b*y, y^2 - 2) with p-adic a, b (precision PREC).
Claim: v_p(B) is negative and odd. Inputs: n = 265, 266, ... until 30 (n, p) cases."""
import cypari2
from sympy import factorint
pari = cypari2.Pari()
PREC = 400
contacts = [0, -15, -20, -24, -30, -60]

def run(n, p):
    O = pari(f"O({p}^{PREC})")
    def k(a, b=0): return pari(f"Mod(({a}) + ({b})*y, y^2-2)") + 0 * O
    def kk(a, b=0):
        return pari.Mod(pari(a) + O + (pari(b) + O) * pari("y"), pari("y^2-2"))
    d = kk(75, -53); A4 = -(d * d)
    P0 = (kk("1641/8", -145), kk("-15465/4", "87483/32"))
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        (x1, y1), (x2, y2) = P, Q
        if pari.valuation(pari.norm(x1 - x2), p) >= PREC // 2:
            lam = (3 * x1 * x1 + A4) / (2 * y1)
        else:
            lam = (y2 - y1) / (x2 - x1)
        x3 = lam * lam - x1 - x2
        return (x3, lam * (x1 - x3) - y1)
    def mul(m, P):
        R, Q = None, P
        while m:
            if m & 1: R = add(R, Q)
            Q = add(Q, Q); m >>= 1
        return R
    conj = lambda u: pari.Mod(pari.subst(pari.lift(u), "y", pari("-y")), pari("y^2-2"))
    w = lambda P: 1 / P[0]
    z = lambda P: -P[0] / P[1]
    h, s0, kap = 2, 2 * n, 1
    Ph, Ps, Phk, Psk = mul(h, P0), mul(s0, P0), mul(h - kap, P0), mul(s0 - kap * n, P0)
    F = 1
    for c in contacts: F *= (n - c)
    eta = 1 if F > 0 else -1
    D = [w(Ph), w(Ps), conj(w(Phk)), conj(w(Psk)), z(Ps) / z(Ph) - n, conj(z(Psk) / z(Phk)) - n]
    R = pari(eta * 2730**6 * F) + O
    W = kk(1)
    for Dj in D:
        C = Dj / F
        W = W * (1 + R * C * C)
    Th = pari.trace(1 / W)
    B = R / (Th * Th)
    return int(pari.valuation(pari(F), p)), int(pari.valuation(B, p))

if __name__ == "__main__":
    rows, n = [], 265
    while len(rows) < 30:
        F = 1
        for c in contacts: F *= (n - c)
        for p, e in sorted(factorint(abs(F)).items()):
            if p > 324 and e % 2 == 1 and len(rows) < 30:
                vF, vB = run(n, p)
                rows.append((n, p, vF, vB))
                print("n=%d p=%d v_p(F)=%d v_p(B)=%d" % rows[-1], flush=True)
        n += 1
    print("cases:", len(rows), " all negative odd:", all(v < 0 and v % 2 for *_, v in rows))
