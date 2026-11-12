"""I4 check (TYZ Lemmas 3.16, 3.18): A(H'_n)_tors = A[(1+i)^3] (order 8, Z/4 x Z/2) for small odd n = 5, 7 mod 8.

H'_d (d = 5 mod 8) is built as in TYZ Prop. 3.2(1): the subfield of the ring class field H_{d,4} of conductor 4
of K_d = Q(sqrt(-d)) fixed by sigma_{1+2 varpi}, varpi = sqrt(-d) - 1 at 2. For K_d != Q(i), Q(sqrt(-3)) the
ring class group of conductor 4 equals the ray class group mod 4 (units +-1 are = 1 mod* 4 up to sign), and the
idele 1+2varpi at 2 has the Artin symbol of the ideal (alpha)^{-1}, alpha = -1 + 2 sqrt(-d) (order 2, so (alpha)).
Then  HH'_n = L_n(i) * prod_{d0 | n, d0 = 5 mod 8} H'_{d0},  L_n(i) = Q(i, sqrt(p) : p | n).
A : 2y^2 = x^3 + x  ~  Y^2 = X^3 + 4X.
Usage: python torsion_H.py n
"""
import sys, time
import cypari2
pari = cypari2.Pari()
pari.allocatemem(4 * 10**9)

n = int(sys.argv[1])
t0 = time.time()
primes = [int(p) for p in pari.factor(n)[0]]


def Hprime(d):
    bnf = pari.bnfinit(f'y^2+{d}', 1)
    bnr = pari.bnrinit(bnf, 4)
    cyc = pari('(b)->b.cyc')(bnr)
    v = pari.bnrisprincipal(bnr, pari(f'-1+2*y'), 0)
    H = pari.mathnf(pari.concat(pari.Mat(v), pari.matdiagonal(cyc)))
    full = pari.bnrclassfield(bnr, 0, 2)          # H_{d,4} (absolute)
    sub = pari.bnrclassfield(bnr, H, 2)            # fixed field of sigma_{1+2 varpi}
    return pari.polredbest(full), pari.polredbest(sub), cyc


def compositum(P, Q):
    c = pari.polcompositum(P, Q)
    # all factors give isomorphic fields only if one of P, Q is Galois; ours are Galois over Q (TYZ F5),
    # so the first factor is the compositum
    return pari.polredbest(c[0])


def has_root(polx, r):
    return len(pari.nfroots(pari.subst(polx, 'x', 'y'), pari(r))) > 0


pol = pari('x^2+1')
for p in primes:
    pol = compositum(pol, pari(f'x^2-{p}'))
d0s = [d for d in range(1, n + 1) if n % d == 0 and d % 8 == 5]
info = []
for d in d0s:
    full, sub, cyc = Hprime(d)
    full = pari.subst(full, 'y', 'x'); sub = pari.subst(sub, 'y', 'x')
    info.append((d, int(pari.poldegree(full)), int(pari.poldegree(sub)), cyc))
    # sanity: H_{d,4} contains sqrt(2), H'_d does not
    r_full = has_root(full, 'x^2-2')
    r_sub = has_root(sub, 'x^2-2')
    print(f'  d0={d}: Cl_4 cyc {cyc}, [H_d4:Q]={info[-1][1]}, [H\'_d:Q]={info[-1][2]}, sqrt2 in H_d4: {r_full}, in H\'_d: {r_sub}')
    pol = compositum(pol, sub)
deg = int(pari.poldegree(pol))
print(f'n={n}: d0 = {d0s}, [HH\'_n:Q] = {deg}  ({time.time()-t0:.1f}s)')
ram = sorted(set(primes + [2]))
nf = pari.nfinit([pol, pari(ram)])
print('  nfinit done', f'{time.time()-t0:.1f}s', ' sqrt2 in HH\'_n:', has_root(pol, 'x^2-2'),
      ' i in HH\'_n:', has_root(pol, 'x^2+1'))
E = pari.ellinit([0, 0, 0, 4, 0], nf)
T = pari.elltors(E)
print(f'  A(HH\'_n)_tors: order {T[0]}, structure {T[1]}  ({time.time()-t0:.1f}s)')
print('  RESULT', 'OK' if int(T[0]) == 8 and [int(x) for x in T[1]] == [4, 2] else 'MISMATCH')
# control: over the full ring class field H_{d,4} of the first d0, sqrt2 is present and A[4] (order 16) should appear
if d0s:
    full, sub, cyc = Hprime(d0s[0])
    full = pari.subst(full, 'y', 'x')
    nf2 = pari.nfinit([full, pari(ram)])
    T2 = pari.elltors(pari.ellinit([0, 0, 0, 4, 0], nf2))
    print(f'  control A(H_{{{d0s[0]},4}})_tors: order {T2[0]}, structure {T2[1]}', 'OK' if int(T2[0]) == 16 else 'UNEXPECTED')
