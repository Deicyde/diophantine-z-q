"""Theorem 3.3 cross-n test for n = 5 mod 8: for every e | n, P_{chi_e} (chi_e <-> K(sqrt e)):
   e = 5,7 mod 8: predicted torsion (Lemma char');
   e = d1 = 1,3 mod 8, d1 > 1: predicted P_{chi_e}(n) = +-2^{h2(n)-h2(d0)} L(d1) P_1(d0), d0 = n/e.
Usage: python tmany.py n1 n2 ...   (one n at a time, sequentially)"""
import sys; sys.path.insert(0, '.')
from heeg import *
I = pari('I')
OM1 = pari('2*intnum(x=[1,-1/2],[oo,-3/2],1/sqrt(x^3-x))')


def kodd(d):
    return len([p for p in pari.factor(d)[0] if p != 2])


def h2(d):
    return kodd(d) if d % 8 == 5 else kodd(d) - 1   # d = 5: disc -4d; d = 7: disc -d


def Lcal(d):
    if d == 1:
        return 1.0
    L = pari('lfun(ellinit([0,0,0,-%d^2,0]),1)' % d)
    val = L / (2 ** (2 * kodd(d) - 3) * OM1 / pari.sqrt(d))
    v = float(val)
    r = round(v ** 0.5) if v > 1e-12 else 0
    assert abs(v - r * r) < 1e-8, (d, v)   # L(d)^2 must be an integer square (TYZ Thm 1.1)
    return v ** 0.5 if v > 0 else 0.0


def forms_all(D, beta):
    h = int(pari.qfbclassno(D))
    amax = 50
    while True:
        reps, allf = heegner_forms(D, beta, amax)
        if len(reps) == h:
            return reps, h
        amax *= 2
        if amax > 6400:
            raise RuntimeError("classes not all hit")


def S_sums(n, es, beta, D):
    reps, h = forms_all(D, beta)
    out = {e: 0 for e in es}
    for Q in reps.values():
        z = zphi(tau_of(Q))
        for e in es:
            out[e] += (1 if e == 1 else genus_char(fund(e), Q, D)) * z
    return out, h


def P1(d0):
    if d0 % 8 == 7:
        S, h = S_sums(d0, [1], delta7(d0), -d0)
        return S[1]
    S, h = S_sums(d0, [1, d0], -8, -64 * d0)
    return (S[1] - I * S[d0]) / 4


def divisors(n):
    return [int(d) for d in pari.divisors(n)]


def run(n):
    assert n % 8 == 5 and pari.issquarefree(n)
    es = divisors(n)
    S, h = S_sums(n, es, -8, -64 * n)
    print("n = %d = %s, h(-64n) = %d, h2(n) = %d" % (n, pari.factor(n), h, h2(n)))
    bad = 0
    for e in es:
        P = (S[e] - I * S[n // e]) / 4        # chi_e psi = chi_{n/e}
        z16 = 16 * P
        if e % 8 in (5, 7):
            ok = in_lattice(z16, 1e-30)
            print("   e=%-6d noncontributing: P torsion: %s" % (e, ok))
            bad += not ok
            continue
        if e == 1:
            print("   e=1      P_1(n) torsion: %s" % in_lattice(z16, 1e-30))
            continue
        d0, d1 = n // e, e
        Ld = Lcal(d1)
        Lr = round(Ld)
        p0 = P1(d0)
        p0tor = in_lattice(16 * p0, 1e-30)
        pred = 16 * 2 ** (h2(n) - h2(d0)) * abs(Lr)
        if p0tor or Lr == 0:
            ok = in_lattice(z16, 1e-30)
            print("   (d0,d1)=(%d,%d) L(d1)=%.4f P_1(d0) torsion=%s: predicted P torsion: %s" % (d0, d1, Ld, p0tor, ok))
            bad += not ok
            continue
        hits = [m for m in range(-4 * pred - 64, 4 * pred + 65) if in_lattice(z16 - m * p0, 1e-30)]
        ok = hits in ([pred], [-pred])
        print("   (d0,d1)=(%d,%d) L(d1)=%.4f 2^(h2(n)-h2(d0))=%d: 16P = m P_1(d0) for m in %s, predicted +-%d: %s"
              % (d0, d1, Ld, 2 ** (h2(n) - h2(d0)), hits, pred, ok))
        bad += not ok
    print("   n=%d mismatches: %d" % (n, bad))
    sys.stdout.flush()


if __name__ == "__main__":
    for a in sys.argv[1:]:
        run(int(a))
