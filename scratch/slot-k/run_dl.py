"""Driver: run the slot construction on admissible inputs and certify with the exact descent.
Usage: python run_dl.py <family>  (needs cypari2 only for factoring theta)."""
import os, sys, random
from fractions import Fraction as Fr
from math import gcd, isqrt, prod
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10 ** 9)
import slotk

def fac(n):
    n = abs(int(n))
    if n <= 1: return {}
    F = pari.factor(n)
    return {int(p): int(e) for p, e in zip(F[0], F[1])}

def admissible(B):
    d = B.denominator
    def vpQ(p):
        def v(n):
            k = 0
            while n % p == 0: n //= p; k += 1
            return k
        return v(B.numerator) - v(B.denominator)
    return isqrt(d) ** 2 == d and 0 < B < Fr(1, 2) and all(vpQ(p) >= 4 for p in slotk.S0)

def run(B, label, all_m=False):
    assert admissible(B), label
    ms = slotk.choose_m(B, fac)
    assert ms, ("no multiplier", label)
    out = []
    for m in (ms if all_m else ms[:1]):
        beta = slotk.sqf(m * B, fac); theta = slotk.sqf(m * (m - B), fac)
        P = sorted(fac(beta)); T = sorted(fac(theta))
        assert theta > 0 and theta % 8 == 1 and gcd(theta, 2730) == 1
        q0, RP, RT = slotk.construct(beta, theta, P, T)
        aux = [q0] + RP + RT
        n = beta * prod(aux)
        c1 = slotk.certified(n, P + aux, beta)
        c2 = slotk.certified(n * theta, P + aux + T, beta)
        ok = c1 in ("torsion", "selmer3") and c2 in ("torsion", "selmer3")
        out.append(ok)
        print(f"{label} m={m} w(beta)={len(P)} w(theta)={len(T)} #aux={len(aux)} "
              f"maxaux_digits={max(len(str(a)) for a in aux)} C_n:{c1} C_ntheta:{c2} {'OK' if ok else 'FAIL'}",
              flush=True)
    return all(out)

def gen_random(rng, ulim=10 ** 7, plist=None, dmult=50):
    while True:
        base = 1
        for p in slotk.S0: base *= p ** rng.randint(4, 7)
        u = prod(plist) if plist else rng.randrange(1, ulim)
        if gcd(u, 2730) != 1: continue
        N = base * u
        lo = isqrt(2 * N) + 1
        while True:
            D = rng.randrange(lo, dmult * lo)
            if gcd(D, N) == 1: break
        B = Fr(N, D * D)
        if admissible(B): return B

if __name__ == "__main__":
    fam = sys.argv[1]
    rng = random.Random(2026)
    if fam == "random30":
        res = [run(gen_random(rng), f"#{i}") for i in range(30)]
    elif fam == "random30all":
        res = [run(gen_random(rng), f"#{i}", all_m=True) for i in range(int(sys.argv[2]) if len(sys.argv) > 2 else 5)]
    else:
        B = Fr(fam)
        res = [run(B, fam, all_m=True)]
    print("ALL OK" if all(res) else "SOME FAIL", sum(res), "/", len(res))
