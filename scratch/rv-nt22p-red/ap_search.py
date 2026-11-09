"""Search for genuine instances of the 14-point pattern of Proposition AP (nt-22p section 3.3):
x, v with u = x + (max S+) v such that every u - c'v, c' in S+ = T ∪ (A' - T), T = C ∪ {1},
A' = A + 10, is a good slope prime (GoodSlopePrime, checked with PARI ellcard), for a v with
prescribed high powers of small primes.  Usage: ap_search.py A v xmax [maxhits]."""
import sys, math
import numpy as np
import gmpy2
import cypari2
pari = cypari2.Pari()

CSET = [0, -15, -20, -24, -30, -60]

def splus(A):
    Ap = A + 10
    T = CSET + [1]
    return sorted(set(T) | {Ap - c for c in T})

def good_slope_prime(p):
    """GoodSlopePrime p: p prime, sqrt 2 exists mod p, 75 -+ 53 r != 0, gcd of the two point
    counts of y^2 = x^3 - (75 -+ 53 r)^2 x equals 4."""
    if not gmpy2.is_prime(p) or p == 2:
        return False
    if pari(f"kronecker(2,{p})") != 1:
        return False
    r = int(pari(f"lift(sqrt(Mod(2,{p})))"))
    d1, d2 = (75 - 53 * r) % p, (75 + 53 * r) % p
    if d1 == 0 or d2 == 0:
        return False
    n1 = int(pari(f"ellcard(ellinit([0,0,0,{-d1*d1 % p},0],{p}))"))
    n2 = int(pari(f"ellcard(ellinit([0,0,0,{-d2*d2 % p},0],{p}))"))
    return math.gcd(n1, n2) == 4

def search(A, v, xmax, maxhits=3, chunk=10**7):
    S = splus(A)
    offs = [max(S) - c for c in S]                     # u - c'v = x + off * v
    P = [int(p) for p in pari(f"primes([2,{min(200000, int(math.isqrt((xmax + max(offs)*v)))+1)}])")]
    # admissible residues of x modulo the small primes dividing v, and mod 8, 7
    hits = []
    x0 = 1
    while x0 <= xmax and len(hits) < maxhits:
        xs = np.arange(x0, min(x0 + chunk, xmax + 1), dtype=np.int64)
        xs = xs[xs % 8 == 1]
        if v % 7 == 0:
            xs = xs[np.isin(xs % 7, [3, 5, 6])]
        for p in P:
            if xs.size == 0:
                break
            forb = np.array(sorted({(-o * v) % p for o in offs}), dtype=np.int64)
            if p == 2:
                continue
            r = xs % p
            keep = ~np.isin(r, forb)
            # values equal to p itself are allowed only if p > 324 (they would be the prime p)
            xs = xs[keep]
            if xs.size < 2000:
                break
        for x in xs.tolist():
            vals = [x + o * v for o in offs]
            if all(good_slope_prime(n) for n in vals):
                hits.append(x)
                print("HIT", A, v, x, flush=True)
                if len(hits) >= maxhits:
                    break
        x0 += chunk
    return hits

if __name__ == "__main__":
    A, v, xmax = int(sys.argv[1]), int(sys.argv[2]), int(float(sys.argv[3]))
    mh = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    print("S+ =", splus(A), "size", len(splus(A)))
    print(search(A, v, xmax, mh))
