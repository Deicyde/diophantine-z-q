# Is the Heegner point tau_Q an "isolated" point of the plane model (j, j_32) of X0(32), i.e. is
# j(32 tau) a simple root of Phi_32(j(tau), Y)?  The roots are j((a tau + b)/d), ad = 32,
# 0 <= b < d, gcd(a, b, d) = 1 (48 of them).  j-values are compared through reduced
# representatives in the standard fundamental domain (no overflow).  Plain Python, double precision.
# Usage: python3 -I isolated_check.py
import math
from math import gcd
def reduce(t):
    for _ in range(10000):
        t = complex(t.real - math.floor(t.real + 0.5), t.imag)
        if abs(t) < 1 - 1e-12: t = -1 / t
        else: break
    return t
def same_j(t1, t2, eps=1e-7):
    r1, r2 = reduce(t1), reduce(t2)
    s = eps * max(1.0, r1.imag)
    if abs(r1 - r2) < s: return True
    if abs(abs(r1.real) - 0.5) < s and abs(abs(r2.real) - 0.5) < s and abs(r1.imag - r2.imag) < s: return True
    if abs(abs(r1) - 1) < s and abs(r1 + r2.conjugate()) < s: return True
    return False
IDX = [(a, b, 32 // a) for a in (1, 2, 4, 8, 16, 32) for b in range(32 // a) if gcd(gcd(a, b), 32 // a) == 1]
def mult(A, B, C):
    D = B * B - 4 * A * C
    tau = (-B + 1j * math.sqrt(-D)) / (2 * A)
    return sum(1 for (a, b, d) in IDX if same_j((a * tau + b) / d, 32 * tau)), D
def delta7(n): return next(d for d in range(128) if (d * d + n) % 128 == 0)
def sqf(n): return all(n % (p * p) for p in range(2, int(n ** 0.5) + 1))
assert len(IDX) == 48
rows = []
for (A, B, C) in [(32, 10, 1), (32, 18, 3), (32, 4, 1), (32, 6, 1), (96, -8, 1)]:
    rows.append(('misc', (A, B, C)))
for n in [5, 13, 21, 29, 37, 53, 61]:
    rows.append((f'tyzForm n={n}', (16 * (n + 1), -8, 1)))
    rows.append((f"tyzForm' n={n}", (16 * (n + 9), -8 * (2 * n + 15), 4 * n + 25)))
for n in [7, 15, 23, 31, 39, 47, 55]:
    if not sqf(n): continue
    d = delta7(n)
    rows.append((f'tyzForm7 n={n}', ((n + d * d) // 4, d, 1)))
    rows.append((f"tyzForm7' n={n}", (32, d, (n + d * d) // 128)))
for name, (A, B, C) in rows:
    m, D = mult(A, B, C)
    print(f'{name:18s} Q=[{A},{B},{C}] D={D} mult={m} {"ISOLATED" if m == 1 else "SINGULAR"}')
