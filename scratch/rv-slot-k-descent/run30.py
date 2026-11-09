"""Run the slot construction (slots.py) on 30 admissible inputs and certify both curves with the
point-based descent (sel2.py).  Usage: python run30.py [first] [last]   (indices into INPUTS)."""
import random
import sys
import time
from fractions import Fraction as Fr
from math import gcd, isqrt, prod

import gmpy2

import slots
from sel2 import selmer, first_coord_contains
from prop0 import prop0_selmer
from sel2 import Span

B1 = Fr(2940617998660874091927347858922135000000, 28396755925539315301025111067910716303889)
B2 = Fr(17280246562649556021336818126510626680000, 80761023146150018763106321014944171609929)
B3 = Fr(4291211885438170688127484392173498582608618500000, 17786998416186532268721491637667246182720797752009)
E11_1 = Fr(1953214331105221068788113059705734448160500000, 13771347816989103342683564720495780320761569449)
STALL = {
    8: Fr(8725822151525970309000000, 1652018862182115577300469089),
    18: Fr(22154089912478417733840000, 74241371343332888001265247689),
    19: Fr(442982398382171657100000, 1097132832331154469090280681),
    20: Fr(224902640413806329520000, 1008742489881490316811506041),
    23: Fr(1389922675279162069500000, 6310448033951315502834721249),
    28: Fr(56139809581010624170338000000, 228122447508138731964199008432601),
}


def core_primes(k, rng):
    K = []
    t = rng.randrange(1, 50)
    while len(K) < k:
        p = 1 + 21840 * t
        t += 1
        if gmpy2.is_prime(p) and all(gmpy2.legendre(p, q) == 1 for q in K):
            K.append(p)
    return K


def make_B(core, rng, cof_bound=1):
    N = prod(p ** rng.randrange(4, 8) for p in slots.S0) * prod(core)
    if cof_bound > 1:
        while True:
            c = rng.randrange(2, cof_bound)
            if gcd(c, 2730) == 1:
                break
        N *= c
    lo = isqrt(2 * N) + 1
    while True:
        D = rng.randrange(lo, 4 * lo)
        if gcd(D, 2730 * N) == 1:
            B = Fr(N, D * D)
            assert slots.admissible(B)
            return B


def inputs():
    rng = random.Random(81108)
    out = [("B1", B1), ("B2", B2), ("B3", B3), ("e11#1", E11_1)]
    out += [("stall#%d" % i, b) for i, b in sorted(STALL.items())]
    for j in range(3):
        out.append(("core3.%d" % j, make_B(core_primes(3, rng), rng)))
    for j in range(2):
        out.append(("core4.%d" % j, make_B(core_primes(4, rng), rng)))
    for j in range(15):
        out.append(("rand.%d" % j, make_B([], rng, cof_bound=10 ** rng.randrange(6, 14))))
    return out


def certify(d, primes, beta, seed):
    gens, ker = selmer(d, primes, seed=seed)
    return len(ker), first_coord_contains(gens, ker, beta), (gens, ker)


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 29
    wrong = len(sys.argv) > 3 and sys.argv[3] == "wrongx"
    INP = inputs()
    for idx in range(lo, hi + 1):
        name, B = INP[idx]
        t0 = time.time()
        assert slots.admissible(B), name
        rng = random.Random(1000 + idx)
        el = slots.eligible(B)
        cand = []
        for m in el:
            beta, theta = slots.beta_theta(B, m)
            cand.append((len(slots.factor(beta)) + len(slots.factor(theta)), m))
        # big inputs: the multiplier with fewest slots; otherwise a random eligible one
        m = min(cand)[1] if name in ("B1", "B2", "B3", "e11#1") else rng.choice(el)
        beta, theta = slots.beta_theta(B, m)
        th = slots.check_theta(beta, theta)
        if wrong and not any(l % 4 == 3 for l in slots.factor(theta)):
            print("#%d %s: theta has no prime = 3 mod 4, skip negative control" % (idx, name), flush=True)
            continue
        c = slots.build(B, m, rng, wrong_x=wrong)
        d1 = abs(c["n"])
        pr1 = sorted(c["P"] + [c["q0"]] + list(c["RP"].values()) + list(c["RT"].values()))
        assert prod(pr1) == d1
        d2 = d1 * theta
        pr2 = sorted(pr1 + c["T"])
        dim1, in1, (g1, k1) = certify(d1, pr1, beta, idx)
        dim2, in2, _ = certify(d2, pr2, beta, idx + 100)
        # Prop 0 on the first curve, as a further differential check
        g0, k0 = prop0_selmer(d1, pr1)
        sa, sb = Span(), Span()
        for v in k1: sa.add(v)
        for v in k0: sb.add(v)
        p0ok = sa.dim() == sb.dim() and all(sa.reduce(v) == 0 for v in k0)
        nslots = 1 + len(c["RP"]) + len(c["RT"])
        digits = max(len(str(q)) for q in [c["q0"]] + list(c["RP"].values()) + list(c["RT"].values()))
        ok = dim1 == 3 and dim2 == 3 and in1 and in2
        print("#%d %s m=%d beta<0=%d |beta|%%8=%d w(beta)=%d w(theta)=%d theta1-4=%s slots=%d (max %d digits) "
              "d1%%8=%d dim1=%d beta_in1=%s dim2=%d beta_in2=%s prop0(d1)=%s %s%s (%.0fs)" % (
                  idx, name, m, c["s"], abs(beta) % 8, len(c["P"]), len(c["T"]),
                  "".join("1" if t else "0" for t in th), nslots, digits, d1 % 8, dim1, in1, dim2, in2,
                  p0ok, "CERTIFIED" if ok else "FAIL", " [wrong x]" if wrong else "",
                  time.time() - t0), flush=True)


if __name__ == "__main__":
    main()
