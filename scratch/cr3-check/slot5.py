"""Step 5: run the slot construction (scratch/slot-k/slotk.py) on admissible B with small
omega(beta), omega(theta); print the prime lists of |n| and |n theta| for evalList in Eval.lean and the
exact-descent verdicts (sel2cong via slotk.certified, and sel2_indep)."""
import os, sys, json, random
from fractions import Fraction as Fr
from math import gcd, isqrt, prod
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'slot-k'))
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10 ** 9)
import slotk
slotk.JAC = lambda x, q: int(pari.kronecker(x, q))
from sel2_indep import first_coords


def fac(n):
    n = abs(int(n))
    if n <= 1: return {}
    F = pari.factor(n)
    return {int(p): int(e) for p, e in zip(F[0], F[1])}


def admissible(B):
    def vpQ(p):
        def v(n):
            k = 0
            while n % p == 0: n //= p; k += 1
            return k
        return v(B.numerator) - v(B.denominator)
    D = B.denominator
    return isqrt(D) ** 2 == D and 0 < B < Fr(1, 2) and all(vpQ(p) >= 4 for p in slotk.S0)


def find_B(rng, wb, wt, force_m=None):
    base = 2 ** 4 * 3 ** 4 * 5 ** 4 * 7 ** 4 * 13 ** 4
    smallp = [p for p in range(11, 400) if pari.isprime(p) and p != 13]
    while True:
        ps = rng.sample(smallp, wb)
        u = prod(ps)
        if u % 8 != 7: continue
        N = base * u
        lo = isqrt(2 * N) + 1
        for _ in range(2000):
            D = rng.randrange(lo, 50 * lo)
            if gcd(D, N) != 1: continue
            B = Fr(N, D * D)
            if not admissible(B): continue
            ms = slotk.choose_m(B, fac)
            if not ms: continue
            m = ms[0] if force_m is None else force_m
            if m not in ms: continue
            beta = slotk.sqf(m * B, fac); theta = slotk.sqf(m * (m - B), fac)
            if len(fac(beta)) == wb and len(fac(theta)) == wt:
                return B, m, beta, theta


rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
cases = []
for label, wb, wt, fm in [('B1', 1, 1, None), ('B2', 1, 2, None), ('B3', 2, 1, None), ('B4', 2, 2, None),
                          ('B5', 1, 1, -1), ('B6', 2, 2, -1)]:
    B, m, beta, theta = find_B(rng, wb, wt, fm)
    P = sorted(fac(beta)); T = sorted(fac(theta))
    q0, RP, RT = slotk.construct(beta, theta, P, T)
    aux = [q0] + RP + RT
    n_pr = sorted(P + aux); nt_pr = sorted(P + aux + T)
    assert all(pari.isprime(p) for p in nt_pr) and len(set(nt_pr)) == len(nt_pr)
    n = prod(n_pr); nt = prod(nt_pr)
    c1 = slotk.certified(n, n_pr, beta); c2 = slotk.certified(nt, nt_pr, beta)
    i1 = first_coords(n, n_pr); i2 = first_coords(nt, nt_pr)
    case = dict(label=label, B=str(B), m=m, beta=beta, theta=theta, P=P, T=T, q0=q0, RP=RP, RT=RT,
                n_primes=n_pr, ntheta_primes=nt_pr, n_mod8=n % 8, nt_mod8=nt % 8,
                sel2cong_n=str(c1), sel2cong_nt=str(c2),
                indep_n=[i1[0], beta in i1[1]], indep_nt=[i2[0], beta in i2[1]])
    cases.append(case)
    print(label, 'B =', B, 'm =', m, 'beta =', beta, 'theta =', theta)
    print('   |n| primes:', len(n_pr), '|n theta| primes:', len(nt_pr), 'max digits', max(len(str(p)) for p in nt_pr),
          '|n| mod 8 =', n % 8, '|n theta| mod 8 =', nt % 8)
    print('   sel2cong:', c1, c2, ' sel2_indep (dim, beta in pi1):', case['indep_n'], case['indep_nt'])
json.dump(cases, open('slot5.json', 'w'), indent=1)
with open('slot5_eval.lean', 'w') as f:
    for c in cases:
        for key in ('n_primes', 'ntheta_primes'):
            f.write('#eval (%r, ZInQ.RouteK.CR3Check.evalList %s [%d])\n' % (c['label'] + ':' + key, str(c[key]), c['beta']))
print(open('slot5_eval.lean').read()[:3000])
