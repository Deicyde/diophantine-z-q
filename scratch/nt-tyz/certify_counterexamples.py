"""Certify the two counterexamples to the literal readings of TYZ Theorem 1.2.

For n in {26565, 33117}:
 1. find three rational points on C_n : y^2 = x^3 - n^2 x and check that their height
    matrix is nonsingular (so rank >= 3; then ord_{s=1} L(C_n, s) != 1 by Gross-Zagier-Kolyvagin,
    the root number is -1 (n = 5 mod 8), hence ord >= 3 and L(n) = 0 by definition);
 2. recompute g(d) for every divisor d of n with a certified class group (bnfinit + bnfcertify),
    and independently by Redei's formula (Smith's Table 1);
 3. recompute T5a, T5b and the (5,1) sums.
"""
import sys
from itertools import combinations

import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)

sys.path.insert(0, ".")
from literal_reading import partitions, prod  # noqa: E402


def g_certified(d):
    K = pari.bnfinit(pari("x^2+%d" % d), 1)
    assert int(pari.bnfcertify(K)) == 1
    cyc = [int(c) for c in K.bnf_get_cyc()]
    return 0 if any(c % 4 == 0 for c in cyc) else 1


def leg(a, p):
    return 0 if int(pari.kronecker(a, p)) == 1 else 1


def det2(M):
    M = [row[:] for row in M]
    n = len(M)
    if n == 0:
        return 1
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, n) if M[i][c]), None)
        if piv is None:
            return 0
        M[r], M[piv] = M[piv], M[r]
        for i in range(n):
            if i != r and M[i][c]:
                M[i] = [(a + b) % 2 for a, b in zip(M[i], M[r])]
        r += 1
    return 1


def g_redei(primes):
    """Smith Table 1 / tyz-5b Prop 2.3, odd d."""
    r = len(primes)
    A = [[0] * r for _ in range(r)]
    for i in range(r):
        for j in range(r):
            if i != j:
                A[i][j] = leg(primes[j], primes[i])
        A[i][i] = sum(A[i]) % 2
    d = prod(primes)
    if d % 4 == 3:
        return det2([row[1:] for row in A[1:]])
    z = [leg(2, p) for p in primes]
    return det2([row[1:] + [z[i]] for i, row in enumerate(A)])


def main():
    for n in (26565, 33117):
        primes = [int(p) for p in pari.factor(n)[0]]
        E = pari.ellinit([0, 0, 0, -n * n, 0])
        print(f"n={n} = {primes}, n mod 8 = {n % 8}, root number = {pari.ellrootno(E)}")
        rk = pari.ellrank(E, 6)
        pts = list(rk[3])
        print(f"  ellrank bounds: {rk[0]}..{rk[1]}, points found: {len(pts)}")
        for P in pts:
            assert int(pari.ellisoncurve(E, P)) == 1
        if len(pts) >= 3:
            H = pari.ellheightmatrix(E, pts[:3])
            print(f"  points: {pts[:3]}")
            print(f"  det(height matrix) = {pari.matdet(H)}")
        gc = {}
        for k in range(1, len(primes) + 1):
            for S in combinations(primes, k):
                d = prod(S)
                a, b = g_certified(d), g_redei(list(S))
                assert a == b, (d, a, b)
                gc[d] = a
        print(f"  g certified (bnfcertify) = Redei on all {len(gc)} divisors; g(n) = {gc[n]}")
        T5a = T5b = S51u = S51d = 0
        for pi in partitions(primes):
            cls = [prod(b) % 8 for b in pi]
            c1 = cls.count(1)
            others = sorted(c for c in cls if c != 1)
            w = prod(gc[prod(b)] for b in pi)
            if others == [5]:
                T5a += w
                if c1 >= 1:
                    S51u += w
                    S51d += c1 * w
            elif others == [3, 7]:
                T5b += w
        print(f"  T5a={T5a % 2} T5b={T5b % 2} (5,1)_unordered,d1>1={S51u % 2} "
              f"(5,1)_distinguished,d1>1={S51d % 2}")
        print(f"  second sum: reading A={(T5a + T5b) % 2}, B={(S51u + T5b) % 2}, C={(S51d + T5b) % 2}")


if __name__ == "__main__":
    main()
