"""Check the coefficient lemma for the genus point recursion of Tian-Yuan-Zhang (n = 5 mod 8).

Abstract model: n = product of r 'primes', each prime carries a class in (Z/8)^* = {1,3,5,7};
g is a random 0/1 function on nonempty subsets.  Lcal(S) for a set S of class 1 or 3 is the
set-partition sum of TYZ Theorem 1.1 (one block of class 3 if class(S)=3, all others class 1).
P(S) for class(S) in {5,7} is defined by the recursion
    P(S) = Z(S) - sum_{T subset S proper nonempty, class(T) in {5,7}, class(S/T) in {1,3}} eps(T,S-T) Lcal(S-T) P(T)
with eps = i if (class T, class S\T) = (5,3) and 1 otherwise (mod 2 the signs do not matter).
We compute the coefficient c_S(T) in Z[i]/2 of Z(T) and compare with
  - for class(T)=7, class(S)=5:  c_S(T) == Lcal(S\T)   (the lemma used for the (7,3) bracket)
  - for class(T)=5, class(S)=5:  report c_S(T) against Lcal(S\T) (the (5,1) bracket; not needed).
Elements of Z[i]/2 are pairs (a,b) mod 2.
Also computes, for S=V, the two brackets C1 = sum_{T=5} c(T) g(T), C2 = sum_{T=7} c(T) g(T), and checks
C2 == T5b(V) and C1 == T5a(V) (as Gaussian integers mod 2).
"""
import random
import sys
from functools import lru_cache
from itertools import combinations


def run(r, seed):
    rnd = random.Random(seed)
    while True:
        cls = [rnd.choice([1, 3, 5, 7]) for _ in range(r)]
        tot = 1
        for c in cls:
            tot = tot * c % 8
        if tot == 5:
            break
    full = (1 << r) - 1
    gv = {m: rnd.randint(0, 1) for m in range(1, full + 1)}

    def cl(m):
        c = 1
        for k in range(r):
            if m >> k & 1:
                c = c * cls[k] % 8
        return c

    @lru_cache(None)
    def parts(m, allowed3):
        """sum over set partitions of m into blocks; allowed3 = number of class-3 blocks required (0/1),
        all other blocks class 1; returns parity of sum of prod g."""
        if m == 0:
            return 1 if allowed3 == 0 else 0
        low = m & -m
        rest = m ^ low
        tot = 0
        sub = rest
        while True:
            b = sub | low
            c = cl(b)
            if c == 1:
                tot += gv[b] * parts(m ^ b, allowed3)
            elif c == 3 and allowed3 == 1:
                tot += gv[b] * parts(m ^ b, 0)
            if sub == 0:
                break
            sub = (sub - 1) & rest
        return tot % 2

    def Lcal(m):
        if m == 0:
            return 1
        c = cl(m)
        assert c in (1, 3)
        return parts(m, 1 if c == 3 else 0)

    def mul(x, y):  # Z[i]/2
        a, b = x
        c, d = y
        return ((a * c - b * d) % 2, (a * d + b * c) % 2)

    @lru_cache(None)
    def coeff(S):
        """dict T -> c_S(T) in Z[i]/2"""
        res = {S: (1, 0)}
        sub = (S - 1) & S
        while sub:
            T = sub
            q = S ^ T
            if cl(T) in (5, 7) and cl(q) in (1, 3):
                L = Lcal(q)
                if L:
                    eps = (0, 1) if (cl(T), cl(q)) == (5, 3) else (1, 0)
                    for U, cu in coeff(T).items():
                        v = mul(eps, cu)
                        old = res.get(U, (0, 0))
                        res[U] = ((old[0] + v[0]) % 2, (old[1] + v[1]) % 2)
            sub = (sub - 1) & S
        return res

    co = coeff(full)
    bad7 = 0
    stats5 = {}
    C1 = (0, 0)
    C2 = 0
    for T, c in co.items():
        if cl(T) == 7:
            if c != (Lcal(full ^ T), 0):
                bad7 += 1
            C2 = (C2 + c[0] * gv[T]) % 2
            assert c[1] == 0
        elif cl(T) == 5:
            key = (c, Lcal(full ^ T))
            stats5[key] = stats5.get(key, 0) + 1
            C1 = ((C1[0] + c[0] * gv[T]) % 2, (C1[1] + c[1] * gv[T]) % 2)
    # T5a, T5b
    T5a = T5b = 0
    for T in range(1, full + 1):
        if cl(T) == 5:
            T5a += gv[T] * Lcal(full ^ T)
        if cl(T) == 7:
            T5b += gv[T] * Lcal(full ^ T)
    return bad7, stats5, C1, C2 == T5b % 2, T5a % 2


def main():
    trials = int(sys.argv[1])
    tot_bad = 0
    agg5 = {}
    c2ok = 0
    c1vs = {}
    for t in range(trials):
        r = 2 + t % 8
        bad7, s5, C1, ok2, T5a = run(r, t)
        tot_bad += bad7
        c2ok += ok2
        for k, v in s5.items():
            agg5[k] = agg5.get(k, 0) + v
        c1vs[(C1, T5a)] = c1vs.get((C1, T5a), 0) + 1
    print(f"trials={trials} (r=2..9): class-7 coefficient mismatches: {tot_bad}; C2==T5b in {c2ok}/{trials}")
    print("class-5 coefficients (c_S(T) in Z[i]/2, Lcal(S/T)) -> count:", agg5)
    print("(C1 in Z[i]/2, T5a) -> count:", c1vs)


if __name__ == "__main__":
    main()
