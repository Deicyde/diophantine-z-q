"""Route K with TYZ certificates: is the TYZ certificate of each converse curve predicted by the
2-adic data of beta alone?

For admissible B (rv-route-k generators) and every signed divisor m of 2730 we search
n = beta * n' (n' = 1, theta, or a product of <= 2 auxiliary primes < AUXB) such that C_n and
C_{n theta} each carry the class beta (torsion point, or dim Sel_2 = 3 with a class of first
coordinate beta).  For each converse curve C_d we compare TYZ (Smith's determinants for |d|)
with the beta-only rules found in tyz_beta_rule.py:
   |d| = 6 (8):  TYZ  <=>  [beta even] != [|beta|_odd = 3 (4)]
   |d| = 5 (8):  [|beta|_odd = 3 (4)]  =>  TYZ
Usage: ktyz_rule_test.py COUNT SEED FAMILY AUXB
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rv-route-k'))
import descent_search as ds
from smith22_check import run


def tyz(d):
    D = run(abs(d), sums=False)[1]
    return int(any(D.values())) if abs(d) % 8 in (5, 6, 7) else 0


def rule(d, beta):
    t = abs(d) % 8
    ev = beta % 2 == 0
    bo = abs(beta) // (2 if ev else 1)
    m3 = bo % 4 == 3
    if t == 6:
        return 'iff', int(ev != m3)
    if t == 5 and m3:
        return 'implies', 1
    return None, None


def main():
    COUNT, SEED, FAM, AUXB = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    rng = random.Random(SEED)
    gen = getattr(ds, 'gen_' + FAM)
    viol = checks = 0
    inputs_with_beta_rule_solution = 0
    for it in range(COUNT):
        B = gen(rng)
        found_rule = False
        nsol = 0
        for m in ds.DIVS:
            beta = ds.sqfQ(m * B); theta = ds.sqfQ(m * (m - B))
            if theta == 1:
                continue
            aux = [p for p in ds.PRIMES if p < AUXB and beta % p and theta % p]
            cands = [1, theta] + aux + [p * q for p, q in itertools.combinations(aux, 2)]
            for npr in cands:
                n = beta * npr
                if ds.sqf_int(n) != n:
                    continue
                g1 = ds.good(n, beta)
                if not g1:
                    continue
                nt = ds.sqf_int(n * theta)
                g2 = ds.good(nt, beta)
                if not g2:
                    continue
                nsol += 1
                conv = [d for d, g in ((n, g1), (nt, g2)) if g == 'selmer3']
                allrule = True
                for d in conv:
                    kind, pred = rule(d, beta)
                    T = tyz(d)
                    if kind == 'iff':
                        checks += 1
                        viol += T != pred
                    elif kind == 'implies':
                        checks += 1
                        viol += T != 1
                    if pred != 1:
                        allrule = False
                if allrule and conv:
                    found_rule = True
                if nsol >= 40:
                    break
            if nsol >= 40 and found_rule:
                break
        inputs_with_beta_rule_solution += found_rule
        print(f"input {it}: solutions examined {nsol}, solution certified by beta-rule alone: {found_rule}", flush=True)
    print(f"rule checks {checks}, violations {viol}; inputs with a beta-rule-certified solution "
          f"{inputs_with_beta_rule_solution}/{COUNT}")


main()
