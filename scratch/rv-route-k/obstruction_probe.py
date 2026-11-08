"""Probe the obstruction to the class beta on C_{n theta}.

For many (B, m): decide empirically whether the class beta ever occurs in Sel_2(C_{n theta}) for
random auxiliary n' (passing the necessary odd-prime conditions), and compare with candidate
invariants built from quartic residue symbols:
  q_theta = prod over p | theta, p = 1 mod 4 of (beta/p)_4      (beta is a square mod p)
  q_beta  = prod over odd p | beta, p = 1 mod 4 of (theta/p)_4  (theta is a square mod p)
  s16     = +1 if theta = 1 mod 16 else -1                       (theta is a 2-adic 4th power iff 1 mod 16)
"""
import sys
import random
from fractions import Fraction as Fr
from collections import Counter
from descent_search import GENS, sqfQ, sqf_int, factor, oddprimes, BIGPOOL, necessary
from sel2cong import selmer, vec_of, first_coord_contains


def quartic(a, p):
    """(a/p)_4 for p = 1 mod 4 and a a nonzero square mod p: +1 or -1."""
    a %= p
    r = pow(a, (p - 1) // 4, p)
    assert r in (1, p - 1), (a, p)
    return 1 if r == 1 else -1


def present_on(beta, theta, rng, trials=150):
    pool = [q for q in BIGPOOL if beta % q != 0 and theta % q != 0][:300]
    hit_n = hit_nt = 0
    done = 0
    while done < trials:
        k = rng.randint(1, 4)
        combo = rng.sample(pool, k)
        prod = 1
        for q in combo:
            prod *= q
        if not necessary(prod, combo, beta):
            continue
        done += 1
        n = beta * prod
        b1, g1 = selmer(n, oddprimes(n))
        nt = sqf_int(n * theta)
        b2, g2 = selmer(nt, oddprimes(nt))
        hit_n += first_coord_contains(b1, vec_of(beta, g1))
        hit_nt += first_coord_contains(b2, vec_of(beta, g2))
    return hit_n, hit_nt


def main():
    fam, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    table = Counter()
    for i in range(count):
        B = GENS[fam](rng)
        for m in [1, 2, 3, 5, 6, 7, -1, -2]:
            beta = sqfQ(m * B)
            theta = sqfQ(m * (m - B))
            if theta == 1:
                continue
            qt = 1
            for p in factor(theta):
                if p % 4 == 1:
                    qt *= quartic(beta, p)
            qb = 1
            for p in factor(beta):
                if p != 2 and p % 4 == 1:
                    qb *= quartic(theta, p)
            s16 = 1 if theta % 16 == 1 else -1
            hn, hnt = present_on(beta, theta, rng)
            obstructed = hnt == 0
            table[(qt, qb, s16, obstructed)] += 1
            print(f"#{i} m={m} beta2={beta % 16 if beta % 2 else 'even'} sign={'+' if beta > 0 else '-'} "
                  f"qt={qt} qb={qb} s16={s16} prod={qt * qb * s16} present(C_n)={hn} present(C_ntheta)={hnt}",
                  flush=True)
    print("(q_theta, q_beta, s16, obstructed): count")
    for k, v in sorted(table.items()):
        print(k, v)


if __name__ == "__main__":
    main()
