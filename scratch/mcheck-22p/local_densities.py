"""mcheck-22p step 3: local densities of the 22 forms (tex L1293-1301, L1418-1428, L1644-1668).
Forms on T=(u1,u2,v): (0,0,1), (1,0,-b), (0,1,-b), (-1,-1,A-b), b in B.
(a) For q = 331, 337 and A in a sample of 6 values: exact count of T in F_q^3 with all F != 0;
    check 1-22/q <= P <= 1-22/q+C(22,2)/q^2 (tex L1421-1424) and log beta_q >= -484/q^2.
(b) Fibre F_nu = c (c != 0 mod q): the other 21 restrictions have distinct zero lines and the
    union has between 21q - C(21,2) and 21q points (tex L1662-1668); q = 331, 4 (nu, A, c) choices.
(c) q <= 324: a residue mod q^5 avoiding all F_nu = 0 mod q^5 exists (proportion <= 22/q^5 < 1).
(d) series bound: q^2 (log(1-22/q) - 22 log(1-1/q)) >= -484 for all q >= 325 (rational majorant).
"""
from fractions import Fraction as Fr
from math import log, comb
from nt import primes_upto

B = [0, -15, -20, -24, -30, -60, 1]
def forms(A):
    F = [(0, 0, 1)]
    F += [(1, 0, -b) for b in B] + [(0, 1, -b) for b in B] + [(-1, -1, A - b) for b in B]
    return F

def count_nonzero(q, A):
    F = forms(A); tot = 0
    for u1 in range(q):
        for u2 in range(q):
            bad = set()
            allv = False
            for (x, y, z) in F:
                c0 = (x * u1 + y * u2) % q; zz = z % q
                if zz == 0:
                    if c0 == 0: allv = True; break
                else:
                    bad.add((-c0 * pow(zz, -1, q)) % q)
            if not allv:
                tot += q - len(bad)
    return tot

print("(a) full-space densities")
ok_a = True
for q in (331, 337):
    for A in (0, 1, -15, 7, 61, 10**9 + 7):
        n = count_nonzero(q, A); P = Fr(n, q ** 3)
        lo, hi = 1 - Fr(22, q), 1 - Fr(22, q) + Fr(comb(22, 2), q * q)
        lb = log(n / q ** 3) - 22 * log(1 - 1 / q)
        ok = lo <= P <= hi and lb >= -484 / q ** 2
        ok_a &= ok
        print(f" q={q} A={A} #nonzero={n} P={float(P):.6f} in[{float(lo):.6f},{float(hi):.6f}] log beta={lb:.3e} >= -484/q^2={-484/q**2:.3e}: {ok}")
print(" (a) all ok:", ok_a)

print("(b) fibres")
ok_b = True
q = 331
for (nu, A, c) in ((0, 0, 5), (3, 2, 1), (17, -40, 100), (21, 61, 330)):
    F = forms(A); Fn = F[nu]
    # parametrize: pick coordinate k with coefficient +-1 in Fn
    k = [i for i in range(3) if Fn[i] in (1, -1)][0]
    others = [i for i in range(3) if i != k]
    lines = set(); union = set()
    for mu, Fm in enumerate(F):
        if mu == nu: continue
        pts = set()
        for s in range(q):
            for t in range(q):
                T = [0, 0, 0]; T[others[0]] = s; T[others[1]] = t
                rest = sum(Fn[i] * T[i] for i in others)
                T[k] = ((c - rest) * Fn[k]) % q  # Fn[k] = +-1 is its own inverse
                if sum(Fm[i] * T[i] for i in range(3)) % q == 0:
                    pts.add((s, t))
        assert len(pts) == q, (mu, len(pts))   # nonconstant restriction: a line
        lines.add(frozenset(pts)); union |= pts
    ok = len(lines) == 21 and 21 * q - comb(21, 2) <= len(union) <= 21 * q
    ok_b &= ok
    print(f" nu={nu} A={A} c={c}: 21 distinct lines={len(lines)==21} |union|={len(union)} in [{21*q-210},{21*q}]: {ok}")
print(" (b) all ok:", ok_b)

print("(c) small primes")
print(" max over q<=324 of 22/q^5 =", Fr(22, 32), "< 1:", all(Fr(22, q ** 5) < 1 for q in primes_upto(324)))

print("(d) series majorant")
# q^2(log(1-22/q) - 22 log(1-1/q)) = -sum_{k>=2} (22^k-22)/(k q^(k-2)) >= -(231 + sum_{k>=3} 22^k/(3 q^(k-2)))
q0 = 325
maj = Fr(231) + Fr(22 ** 3, 3 * q0) / (1 - Fr(22, q0))
print(f" majorant at q=325 (decreasing in q): {float(maj):.4f} <= 484: {maj <= 484}")
print(" spot values q^2*(...):", [(qq, round(qq * qq * (log(1 - 22 / qq) - 22 * log(1 - 1 / qq)), 3)) for qq in (331, 1009, 10**5)])
