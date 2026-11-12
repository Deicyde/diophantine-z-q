"""Acceptance tests for TateNormalForm.lean / node MC2: on E(b,c): y^2+(1-c)xy-by = x^3-bx^2,
P=(0,0); check symbolically that P has exact order N on Kubert's genus-0 families, N = 4..10 (a remembered N = 12 family was wrong and is dropped).
Families (Kubert 1976, Table 3; from memory, UNVERIFIED locators)."""
from sympy import symbols, simplify, together, factor, Rational
t = symbols('t')

def add(P, Q, a1, a2, a3, a4, a6):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if simplify(x1 - x2) == 0:
        if simplify(y1 + y2 + a1 * x2 + a3) == 0: return None
        l = (3 * x1**2 + 2 * a2 * x1 + a4 - a1 * y1) / (2 * y1 + a1 * x1 + a3)
    else:
        l = (y1 - y2) / (x1 - x2)
    l = together(l)
    x3 = together(l**2 + a1 * l - a2 - x1 - x2)
    y3 = together(-(y1 + l * (x3 - x1)) - a1 * x3 - a3)
    return (factor(x3), factor(y3))

def order(b, c, bound=20):
    a1, a2, a3, a4, a6 = 1 - c, -b, -b, 0, 0
    P = (0 * t, 0 * t); Q = P
    for n in range(1, bound + 1):
        if Q is None: return n
        Q = add(Q, P, a1, a2, a3, a4, a6)
    return None

fam = {
    4: (t, 0 * t), 5: (t, t), 6: (t + t**2, t),
    7: (t**3 - t**2, t**2 - t),
    8: ((2 * t - 1) * (t - 1), (2 * t - 1) * (t - 1) / t),
    9: (t**2 * (t - 1) * (t**2 - t + 1), t**2 * (t - 1)),
    10: (t**3 * (t - 1) * (2 * t - 1) / (t**2 - 3 * t + 1)**2, -t * (t - 1) * (2 * t - 1) / (t**2 - 3 * t + 1)),
}
for N, (b, c) in fam.items():
    print(N, "order of (0,0):", order(b, c))
