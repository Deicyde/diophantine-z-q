"""Exact arithmetic in K0 = Q(sqrt2) and the test-site pole input of the Lean definitions
(SixLocalTests.lean: testD, testR0, testR, poleW, poleTheta, testC; Curve.lean: genP0, genD)."""
from fractions import Fraction as Fr

class K:
    __slots__ = ("a", "b")
    def __init__(s, a, b=0): s.a = Fr(a); s.b = Fr(b)
    def __add__(s, o): o = K.c(o); return K(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __sub__(s, o): o = K.c(o); return K(s.a - o.a, s.b - o.b)
    def __rsub__(s, o): return K.c(o) - s
    def __mul__(s, o): o = K.c(o); return K(s.a*o.a + 2*s.b*o.b, s.a*o.b + s.b*o.a)
    __rmul__ = __mul__
    def __neg__(s): return K(-s.a, -s.b)
    def norm(s): return s.a*s.a - 2*s.b*s.b
    def conj(s): return K(s.a, -s.b)
    def inv(s): n = s.norm(); return K(s.a/n, -s.b/n)
    def __truediv__(s, o): return s * K.c(o).inv()
    def __rtruediv__(s, o): return K.c(o) * s.inv()
    def __eq__(s, o): o = K.c(o); return s.a == o.a and s.b == o.b
    def iszero(s): return s.a == 0 and s.b == 0
    @staticmethod
    def c(o): return o if isinstance(o, K) else K(o)
    def __repr__(s): return f"({s.a} + {s.b}s)"

D = K(75, -53)
A4 = -(D*D)                      # y^2 = x^3 + A4 x
P0 = (K(Fr(1641, 8), -145), K(Fr(-15465, 4), Fr(87483, 32)))
assert P0[1]*P0[1] == P0[0]*P0[0]*P0[0] + A4*P0[0]

def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2:
        if (y1 + y2).iszero(): return None
        lam = (3*x1*x1 + A4) / (2*y1)
    else:
        lam = (y2 - y1) / (x2 - x1)
    x3 = lam*lam - x1 - x2
    return (x3, lam*(x1 - x3) - y1)

def neg(P): return None if P is None else (P[0], -P[1])

def smul(n, P=P0):
    if n < 0: return smul(-n, neg(P))
    R, Q = None, P
    while n:
        if n & 1: R = add(R, Q)
        Q = add(Q, Q); n >>= 1
    return R

def w(P): return K(0) if P is None else 1 / P[0]
def z(P): return K(0) if P is None else -P[0] / P[1]

CONTACT = [0, -15, -20, -24, -30, -60]
def F(t):
    r = Fr(1)
    for c in CONTACT: r *= (t - c)
    return r

def testD(n, kap, t, h, s0):
    Ph, Ps, Phk, Psk = smul(h), smul(s0), smul(h - kap), smul(s0 - kap*n)
    return [w(Ph), w(Ps), w(Phk).conj(), w(Psk).conj(),
            z(Ps)/z(Ph) - t, (z(Psk)/z(Phk)).conj() - t]

def testC(n, kap, t, h, s0):
    f = F(t)
    return [d / f for d in testD(n, kap, t, h, s0)]

def testR0(eta, t): return eta * Fr(2730)**6 * F(t)

def theta(R, C):
    W = K(1)
    for c in C: W = W * (1 + R*c*c)
    if W.iszero(): return None
    return 2 * W.inv().a

def testB(n, kap, eta, q, h, s0, C=None):
    t = Fr(n)
    if C is None: C = testC(n, kap, t, h, s0)
    R0 = testR0(eta, t); a0 = 1 - R0*q*q
    R = R0*a0*a0
    Th = theta(R, C)
    if a0 == 0 or Th is None or Th == 0: return None
    return R / (Th*Th)
