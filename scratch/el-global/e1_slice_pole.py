"""E1: on a slice with genuine labels (n, kappa fixed, h = 2kappa, s0 = 2kappa n), the test-site pole
input B(t, q) = R/Theta^2 has an odd pole along t = c for every contact c (SixLocalTests.lean).
Exact arithmetic in K0 = Q(sqrt2); truncated Laurent series in e = t - c.
Inputs: 5 pairs (n, kappa) x 6 contacts = 30 cases; q = 3/7 fixed, eta = 1.
Output: v_e(B) for each case."""
from fractions import Fraction as Fr

class K:  # a + b sqrt2
    __slots__ = ("a", "b")
    def __init__(s, a, b=0): s.a, s.b = Fr(a), Fr(b)
    def __add__(s, o): o = o if isinstance(o, K) else K(o); return K(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __neg__(s): return K(-s.a, -s.b)
    def __sub__(s, o): return s + (-(o if isinstance(o, K) else K(o)))
    def __rsub__(s, o): return K(o) - s
    def __mul__(s, o): o = o if isinstance(o, K) else K(o); return K(s.a*o.a + 2*s.b*o.b, s.a*o.b + s.b*o.a)
    __rmul__ = __mul__
    def conj(s): return K(s.a, -s.b)
    def norm(s): return s.a*s.a - 2*s.b*s.b
    def inv(s): n = s.norm(); return K(s.a/n, -s.b/n)
    def __truediv__(s, o): o = o if isinstance(o, K) else K(o); return s * o.inv()
    def iszero(s): return s.a == 0 and s.b == 0

d = K(75, -53); A4 = -(d*d)
P0 = (K(Fr(1641, 8), -145), K(Fr(-15465, 4), Fr(87483, 32)))
assert (P0[1]*P0[1] - (P0[0]*P0[0]*P0[0] + A4*P0[0])).iszero()

def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if (x1 - x2).iszero():
        if (y1 + y2).iszero(): return None
        lam = (3*x1*x1 + A4) / (2*y1)
    else:
        lam = (y2 - y1) / (x2 - x1)
    x3 = lam*lam - x1 - x2
    return (x3, lam*(x1 - x3) - y1)

def mul(k, P):
    if k < 0: R = mul(-k, P); return None if R is None else (R[0], -R[1])
    R, Q = None, P
    while k:
        if k & 1: R = add(R, Q)
        Q = add(Q, Q); k >>= 1
    return R

w = lambda P: P[0].inv()
z = lambda P: -(P[0] / P[1])

N = 16  # series precision
def s_mul(f, g):
    h = [K(0)] * N
    for i, a in enumerate(f):
        if a.iszero(): continue
        for j in range(N - i):
            h[i+j] = h[i+j] + a*g[j]
    return h
def s_inv(f):  # f[0] != 0
    g = [K(0)] * N; g[0] = f[0].inv()
    for k in range(1, N):
        acc = K(0)
        for i in range(1, k+1): acc = acc + f[i]*g[k-i]
        g[k] = -(acc * g[0])
    return g
def val(f):
    for i, a in enumerate(f):
        if not a.iszero(): return i
    return None
# Laurent series = (shift, list) with value e^shift * list

contacts = [0, -15, -20, -24, -30, -60]
def poly_series(c):  # F(t) at t = c + e, as a power series with rational coeffs
    f = [K(1)] + [K(0)]*(N-1)
    for r in contacts:
        f = s_mul(f, [K(c - r), K(1)] + [K(0)]*(N-2))
    return f

def case(n, kap, c, q=Fr(3, 7), eta=1):
    h, s0 = 2*kap, 2*kap*n
    Ph, Ps, Phk, Psk = mul(h, P0), mul(s0, P0), mul(h - kap, P0), mul(s0 - kap*n, P0)
    r5 = z(Ps) / z(Ph); r6 = (z(Psk) / z(Phk)).conj()
    # D_j as power series in e (t = c + e)
    Ds = [[w(Ph)], [w(Ps)], [w(Phk).conj()], [w(Psk).conj()], [r5 - c, K(-1)], [r6 - c, K(-1)]]
    Ds = [D + [K(0)]*(N - len(D)) for D in Ds]
    F = poly_series(c)
    vF = val(F); assert vF == 1
    Fu = F[vF:] + [K(0)]*vF  # F = e * Fu
    R0 = [eta * 2730**6 * x for x in Fu]  # R0 = e * R0u
    # a0 = 1 - R0 q^2 = 1 - e R0u q^2
    a0 = [K(1)] + [K(0)]*(N-1)
    for i in range(N-1): a0[i+1] = a0[i+1] - R0[i]*q*q
    Ru = s_mul(R0, s_mul(a0, a0))  # R = e * Ru
    Fu_inv = s_inv(Fu)
    # R C_j^2 = e Ru D_j^2 / (e^2 Fu^2) = e^{-1} Ru D_j^2 Fu^{-2}
    # 1 + R C_j^2 = e^{-1} (e + Ru D_j^2 Fu^{-2}) =: e^{-1} G_j
    Wu = [K(1)] + [K(0)]*(N-1)  # W = e^{-6} prod G_j
    for D in Ds:
        T = s_mul(Ru, s_mul(s_mul(D, D), s_mul(Fu_inv, Fu_inv)))
        G = T[:]; G[1] = G[1] + K(1)
        assert val(G) == 0
        Wu = s_mul(Wu, G)
    Winv = s_inv(Wu)  # W^{-1} = e^6 Winv
    Th = [K(2*x.a) for x in Winv]  # Tr, as K with b = 0;  Theta = e^6 Th
    vTh = val(Th)
    # B = R / Theta^2 = e^{1 - 12 - 2 vTh} * unit
    return 1 - 12 - 2*vTh, vTh

if __name__ == "__main__":
    pairs = [(2, 1), (3, 1), (5, 2), (-3, 1), (4, 1)]
    out = []
    for n, kap in pairs:
        for c in contacts:
            vB, vTh = case(n, kap, c)
            out.append(vB)
            print(f"n={n:3d} kappa={kap} c={c:4d}  v_e(Theta)-6={vTh}  v_e(B)={vB}")
    print("all odd:", all(v % 2 for v in out), " values:", sorted(set(out)))
