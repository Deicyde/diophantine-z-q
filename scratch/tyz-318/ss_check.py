# VERIFIED-check of leaf SupersingularExponentA on samples (pure Python, no PARI):
# for p = 3 mod 4, every point of y^2 = x^3 + 4x over F_{p^2} = F_p[t]/(t^2+1) is killed by p+1,
# and the group has (p+1)^2 points; over F_p it has p+1 points.
import sys
def run(p):
    # elements a + b t, t^2 = -1
    def mul(u, v): return ((u[0]*v[0]-u[1]*v[1]) % p, (u[0]*v[1]+u[1]*v[0]) % p)
    def add(u, v): return ((u[0]+v[0]) % p, (u[1]+v[1]) % p)
    def sub(u, v): return ((u[0]-v[0]) % p, (u[1]-v[1]) % p)
    def pw(u, e):
        r = (1, 0)
        while e:
            if e & 1: r = mul(r, u)
            u = mul(u, u); e >>= 1
        return r
    q = p*p
    def inv(u): return pw(u, q-2)
    F = [(a, b) for a in range(p) for b in range(p)]
    sq = {}
    for y in F: sq.setdefault(mul(y, y), []).append(y)
    four = (4 % p, 0); three = (3 % p, 0); two = (2 % p, 0)
    pts = [None]
    for x in F:
        r = add(mul(mul(x, x), x), mul(four, x))
        for y in sq.get(r, []): pts.append((x, y))
    def padd(P, Q):
        if P is None: return Q
        if Q is None: return P
        if P[0] == Q[0]:
            if add(P[1], Q[1]) == (0, 0): return None
            lam = mul(add(mul(three, mul(P[0], P[0])), four), inv(mul(two, P[1])))
        else:
            lam = mul(sub(Q[1], P[1]), inv(sub(Q[0], P[0])))
        x3 = sub(sub(mul(lam, lam), P[0]), Q[0])
        y3 = sub(mul(lam, sub(P[0], x3)), P[1])
        return (x3, y3)
    def smul(n, P):
        R = None
        while n:
            if n & 1: R = padd(R, P)
            P = padd(P, P); n >>= 1
        return R
    killed = all(smul(p+1, P) is None for P in pts)
    n1 = sum(1 for P in pts if P is None or (P[0][1] == 0 and P[1][1] == 0))
    return len(pts), n1, killed
for p in [3, 7, 11, 19, 23, 31, 43, 47]:
    N2, N1, k = run(p)
    print(p, "#E(F_p^2) =", N2, "(p+1)^2 =", (p+1)**2, "#E(F_p) =", N1, "killed by p+1:", k,
          "OK" if (N2 == (p+1)**2 and N1 == p+1 and k) else "FAIL")
