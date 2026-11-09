"""Validation families for the slot construction (see docs/research/slot-k.md §3).
Usage: python run_families.py FAMILY   with FAMILY in
  B123 | stall | core3 | core6 | e11 | smooth | allm"""
import os, sys, random
from fractions import Fraction as Fr
from math import prod, gcd
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(1, os.path.join(HERE, "..", "rv-route-k"))
import run_dl, slotk
from run_dl import run, fac, gen_random, admissible

B123 = ["2940617998660874091927347858922135000000/28396755925539315301025111067910716303889",
        "17280246562649556021336818126510626680000/80761023146150018763106321014944171609929",
        "4291211885438170688127484392173498582608618500000/17786998416186532268721491637667246182720797752009"]
STALL = ["8725822151525970309000000/1652018862182115577300469089",
         "22154089912478417733840000/74241371343332888001265247689",
         "442982398382171657100000/1097132832331154469090280681",
         "224902640413806329520000/1008742489881490316811506041",
         "1389922675279162069500000/6310448033951315502834721249",
         "56139809581010624170338000000/228122447508138731964199008432601"]
E11 = ["4291211885438170688127484392173498582608618500000/17786998416186532268721491637667246182720797752009",
       "1953214331105221068788113059705734448160500000/13771347816989103342683564720495780320761569449"]


def core(K):
    c, p = [], 1
    while len(c) < K:
        p += 21840
        if slotk.is_prime(p) and all(pow(p, (x - 1) // 2, x) == 1 for x in c):
            c.append(p)
    return c


def run_m(B, m, label):
    """Run the construction for one prescribed multiplier."""
    beta = slotk.sqf(m * B, fac); theta = slotk.sqf(m * (m - B), fac)
    assert beta % 2 and abs(beta) % 8 == 7
    P = sorted(fac(beta)); T = sorted(fac(theta))
    q0, RP, RT = slotk.construct(beta, theta, P, T)
    aux = [q0] + RP + RT; n = beta * prod(aux)
    c1 = slotk.certified(n, P + aux, beta); c2 = slotk.certified(n * theta, P + aux + T, beta)
    ok = c1 in ("torsion", "selmer3") and c2 in ("torsion", "selmer3")
    print(f"{label} m={m} w(beta)={len(P)} w(theta)={len(T)} #aux={len(aux)} C_n:{c1} C_ntheta:{c2} "
          f"{'OK' if ok else 'FAIL'}", flush=True)
    return ok


if __name__ == "__main__":
    fam = sys.argv[1]; res = []
    rng = random.Random(77)
    if fam == "B123":
        res = [run(Fr(b), f"B{i+1}", all_m=True) for i, b in enumerate(B123)]
    elif fam == "stall":
        res = [run(Fr(b), f"stall{i}", all_m=True) for i, b in enumerate(STALL)]
    elif fam == "e11":
        res = [run(Fr(b), f"e11#{i}", all_m=True) for i, b in enumerate(E11)]
    elif fam in ("core3", "core6"):
        K = int(fam[4:]); c = core(K); print("core", c)
        res = [run(gen_random(rng, plist=c, dmult=2), f"{fam}#{i}", all_m=True) for i in range(3)]
    elif fam == "smooth":
        import descent_search as DS
        cnt = 0
        while cnt < 10:
            B = DS.gen_smooththeta(rng)
            beta = slotk.sqf(B, fac)
            if beta % 2 == 0 or abs(beta) % 8 != 7:
                continue
            res.append(run_m(B, 1, f"smooth#{cnt} theta1={slotk.sqf(1 - B, fac)}"))
            cnt += 1
    elif fam == "allm":
        res = [run(gen_random(rng), f"allm#{i}", all_m=True) for i in range(5)]
    print("ALL OK" if all(res) else "SOME FAIL", sum(res), "/", len(res))
