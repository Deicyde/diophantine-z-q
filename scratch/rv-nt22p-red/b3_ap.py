"""Batch 3: Proposition AP end to end on genuine pattern instances (found by ap_search.py).
For (A, v, x): u = x + (max S+) v, t1 = u/v, t2 = A' - u/v, t3 = -10.  For each slope:
fields 1, 2' (field 2 or Lemma P hypotheses at every prime of the model S_b), 3, 4 checked from
the definitions; then q by the modified weak approximation, model test values with one group
assigned to each odd contact prime, and the pole input: v_p(B) at S_b, at the selected primes,
at every prime of num/den of R0, at the auxiliary prime; reduced denominator over these
primes; 0 < B < 1/2."""
import sys, random, math, time
from fractions import Fraction as Fr
import slopelib as L
from ap_search import splus, good_slope_prime

H = [331, 337]
Sb = L.S_HT + H
ELL0 = L.ell0(H)
rng = random.Random(11)

def factor_primes(n):
    n = abs(int(n))
    if n <= 1:
        return []
    return [int(p) for p in L.pari(f"factor({n})[,1]")]

def odd_contact_primes(t):
    out = set()
    for c in L.CSET:
        for p in factor_primes((t - c).numerator):
            vv = L.vp(t - c, p)
            if vv > 0 and vv % 2 == 1:
                out.add(p)
    return sorted(out)

def check_slope(name, t, mode="new", dmode="random", verbose=True):
    res = {"name": name}
    # field 1
    f1 = t not in [Fr(c) for c in L.CSET] and t != 1
    # field 2'
    f2 = {}
    for l in Sb:
        if L.field2_holds(t, l):
            f2[l] = "f2"
        elif L.lemmaP_hyp(t, l):
            f2[l] = "P"
        else:
            f2[l] = "FAIL"
    f2ok = all(x != "FAIL" for x in f2.values())
    Spole = [l for l in Sb if f2[l] == "P"] if mode == "new" else \
            [l for l in Sb if f2[l] == "P" and l in L.S0]
    # field 3, 4
    oc = [p for p in odd_contact_primes(t) if p not in Sb]
    f3 = all(good_slope_prime(p) and all(L.vp(t - c, p) <= 1 for c in L.CSET) for p in oc)
    f4 = len(oc) <= 6
    eta = 1 if L.F(t) > 0 else -1
    R0 = L.R0_of(t, eta)
    D = L.model_tests(oc, rng, mode=dmode)
    Dmax = max(abs(x) + 1.5 * abs(y) for row in D for (x, y) in row) + 1
    Cmax = max(math.log10(Dmax) - k * math.log10(abs(float(R0))) - (k + 1) * math.log10(abs(float(t - 1))) for k in (1, 25))
    Nl = {l: 23 * L.vp_int(t.denominator, l) + L.vp_int(12, l) + 2 for l in Spole}
    avoid = set(oc)
    for c in L.CSET + [1]:
        avoid |= set(factor_primes((t - c).numerator))
    avoid |= set(factor_primes(t.denominator))
    q, info = L.choose_q(t, eta, Sb, Spole, Nl, oc, avoid, ELL0, Cmax_log10=Cmax)
    P = L.PoleInput(t, eta, q, ELL0, D)
    check = sorted(set(Sb) | set(oc) | avoid | {info["Laux"]})
    vB = {}
    for p in check:
        r = P.local(p)
        vB[p] = r["vB"]
    rl = P.real()
    s0 = {l: vB[l] for l in L.S0}
    sel = {p: vB[p] for p in oc}
    odd_other = {p: vB[p] for p in check if p not in oc and (vB[p] is None or vB[p] % 2)}
    neg = {p: -vB[p] for p in check if vB[p] is not None and vB[p] < 0}
    den_sq = all(e % 2 == 0 for e in neg.values())
    ok = (f1 and f2ok and f3 and f4 and all(x is not None and x >= 4 for x in s0.values())
          and all(x == 1 for x in sel.values()) and den_sq and 0 < rl["B"] < 0.5)
    if verbose:
        print(f"  [{name}] t = {t.numerator}/{t.denominator}  eta={eta:+d}  F(t)>0: {L.F(t) > 0}")
        print(f"    fields: 1 {f1} | 2' {f2ok} (Lemma P branch at {[l for l in Sb if f2[l]=='P']}) | "
              f"3 {f3} | 4 {f4} (odd contact primes outside S_b: {oc})")
        print(f"    v_l(B) on S0: {s0}; Spole used: {Spole}; v_l(a) on Spole: {[P.v_a(l) for l in Spole]}")
        print(f"    v_p(B) at selected primes: {sel}")
        print(f"    primes with odd v_p(B) besides selected: {odd_other}")
        print(f"    checked part of den(B): primes {sorted((p, e) for p, e in neg.items() if p != info['Laux'])}"
              f" + Laux^{neg.get(info['Laux'])}; square: {den_sq}")
        print(f"    0 < B < 1/2: {0 < rl['B'] < 0.5}  (log10 B = {float(L.mpmath.log10(rl['B'])):.1f}); "
              f"q has {L.gmpy2.num_digits(L.mpz(q.denominator), 10)} digits; ALL OK: {ok}")
    return ok

def run_instance(A, v, x, dmode="random"):
    Ap = A + 10
    S = splus(A)
    u = x + max(S) * v
    vals = [u - c * v for c in S]
    print(f"Instance A={A} v={v} = {dict(L.pari(f'factor({v})').mattranspose().Vec()) if False else L.pari(f'factor({v})')} x={x}; |S+|={len(S)}")
    print(f"  all {len(vals)} values good slope primes > max S_b: {all(good_slope_prime(n) and n > max(Sb) for n in vals)}")
    t1 = Fr(u, v)
    t2 = Fr(Ap) - t1
    oks = [check_slope("t1", t1, dmode=dmode), check_slope("t2", t2, dmode=dmode),
           check_slope("t3=-10", Fr(-10), dmode=dmode)]
    print(f"  t1 + t2 + t3 == A: {t1 + t2 - 10 == A};  all slopes OK: {all(oks)}")
    return all(oks)

if __name__ == "__main__":
    A, v, x = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    dmode = sys.argv[4] if len(sys.argv) > 4 else "random"
    run_instance(A, v, x, dmode)
