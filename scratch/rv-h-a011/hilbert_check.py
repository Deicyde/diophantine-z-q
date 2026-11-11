"""Hilbert symbols (a,b)_v for B=(a,b) over Q at v in {inf,2,3,5,7}: which places ramify.
Used for route (a) (Lemma PG needs B ramified at 3, i.e. B (x) Q_3 division).
Formulas: Serre, A Course in Arithmetic, Ch. III, Thm 1."""
import sys
def val(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k, n
def legendre(u, p):
    r = pow(u % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else r
def hilbert(a, b, p):
    if p == 'inf':
        return -1 if (a < 0 and b < 0) else 1
    al, u = val(a, p); be, v = val(b, p)
    if p != 2:
        s = (-1) ** (al * be * ((p - 1) // 2))
        return s * legendre(u, p) ** be * legendre(v, p) ** al
    eps = lambda x: ((x - 1) // 2) % 2
    om = lambda x: ((x * x - 1) // 8) % 2
    e = eps(u) * eps(v) + al * om(v) + be * om(u)
    return (-1) ** (e % 2)
a, b = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (2, -3)
ram = [p for p in ['inf', 2, 3, 5, 7] if hilbert(a, b, p) == -1]
print(f"B=({a},{b}): ramified among inf,2,3,5,7 at {ram}")
