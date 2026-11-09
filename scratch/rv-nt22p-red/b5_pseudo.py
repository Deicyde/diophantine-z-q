"""Batch 5.
Part A: pseudo-instances of the Prop AP pattern with huge powers of old primes in v: the |S+|
values u - c'v are S_b-units (coprime to every prime of the model S_b) but not required to be
prime.  Everything at the old primes and at the real place is then exactly as for a genuine
instance; contact primes are not modelled (random test values in all groups).  Checks field 2'
at every prime of S_b and v_l(B) at S0 / parity on S_b / 0 < B < 1/2 for t1 and t2.
Part B: Lemma P(3) in isolation: ell0 replaced by ell0 / l^{E_l} (so v_l(ell0) = 0), with the
Lemma P ball (expected: v_l(B) >= 4) and with the old choice v_l(q) >= C_l (expected failure)."""
import random, math, time, sys
from fractions import Fraction as Fr
import slopelib as L
from ap_search import splus

H = [331, 337]
Sb = L.S_HT + H
ELL0 = L.ell0(H)
PSb = 1
for p in Sb:
    PSb *= p
rng = random.Random(5)

def sb_check(lab, t, ell0_val, mode="new", only=None):
    eta = 1 if L.F(t) > 0 else -1
    R0 = L.R0_of(t, eta)
    f2 = {l: ("f2" if L.field2_holds(t, l) else ("P" if L.lemmaP_hyp(t, l) else "FAIL")) for l in Sb}
    if mode == "new":
        Spole = [l for l in Sb if f2[l] == "P"]
    elif mode == "S0only":
        Spole = [l for l in L.S0 if f2[l] == "P"]
    elif mode == "force":
        Spole = [l for l in L.S0 if L.lemmaP_hyp(t, l)]
    else:
        Spole = []
    D = L.model_tests([], rng)
    Dmax = max(abs(x) + 1.5 * abs(y) for row in D for (x, y) in row) + 1
    Cmax = max(math.log10(Dmax) - k * float(L.mpmath.log10(abs(L.mpmath.mpf(R0.numerator) / R0.denominator)))
               - (k + 1) * float(L.mpmath.log10(abs(L.mpmath.mpf((t - 1).numerator) / (t - 1).denominator)))
               for k in (1, 25))
    Nl = {l: 23 * L.vp_int(t.denominator, l) + L.vp_int(12, l) + 2 for l in Spole}
    q, info = L.choose_q(t, eta, Sb, Spole, Nl, [], [], ell0_val, Cmax_log10=max(Cmax, 0))
    P = L.PoleInput(t, eta, q, ell0_val, D)
    primes = only if only else [l for l in Sb if L.vp_int(t.denominator, l) > 0 or l in L.S0]
    vB = {l: P.local(l)["vB"] for l in primes}
    rl = P.real()
    s0 = all(vB[l] is not None and vB[l] >= 4 for l in L.S0 if l in vB)
    oddneg = [l for l in vB if vB[l] is None or (vB[l] < 0 and vB[l] % 2)]
    negev = {l: vB[l] for l in vB if vB[l] is not None and vB[l] < 0}
    print(f"  {lab}: eta={eta:+d} field2' ok: {all(x != 'FAIL' for x in f2.values())} "
          f"LemmaP-branch={[l for l in Sb if f2[l]=='P']} Spole={Spole}\n"
          f"     v_l(B)={vB}  S0>=4: {s0}  odd-negative: {oddneg}  negative-even: {negev}  "
          f"0<B<1/2: {0 < rl['B'] < 0.5}", flush=True)
    return s0, oddneg, rl

def pseudo_x(A, v):
    S = splus(A)
    offs = [max(S) - c for c in S]
    while True:
        x = rng.randint(1, 10**15)
        if all(math.gcd(x + o * v, PSb) == 1 for o in offs):
            return x

part = sys.argv[1] if len(sys.argv) > 1 else "AB"
if "A" in part:
    print("Part A: pseudo-instances")
    cases = [(-70, 2**40 * 3 * 7 * 11), (-69, 2**40 * 3**30), (0, 2**20 * 3**20 * 5**20 * 7**20 * 13**20),
             (5, 2**200 * 3 * 7), (-1000, 13**150 * 2 * 3 * 7), (10**6, 331**5 * 337**3 * 2**7 * 3 * 7),
             (-68, 5**130 * 2 * 3 * 7), (-40, 7**150 * 2**3 * 3), (1, 2**5 * 3**5 * 5**5 * 7**5 * 13**5 * 11**5),
             (-71, 2**3 * 3 * 7 * 11**80 * 17**60)]
    for A, v in cases:
        x = pseudo_x(A, v)
        S = splus(A)
        u = x + max(S) * v
        t1 = Fr(u, v); t2 = Fr(A + 10) - t1
        print(f"A={A} v={L.pari(f'factor({v})')} x={x}")
        sb_check("t1", t1, ELL0)
        sb_check("t2", t2, ELL0)
if "B" in part:
    print("Part B: Lemma P(3) with v_l(ell0) = 0")
    for l, e in [(2, 3), (2, 7), (3, 1), (3, 9), (5, 2), (7, 4), (13, 1), (13, 6), (5, 30), (7, 60)]:
        v = l ** e
        while True:
            u = rng.randint(2 * v, 60 * v)
            if math.gcd(u, v) == 1:
                break
        t = Fr(u, v)
        e0 = ELL0 // L.mpz(l) ** L.Ep(l)
        assert L.vp_int(e0, l) == 0
        print(f"l={l} e={e} t={u}/{v}")
        sb_check("ball", t, e0, mode="force", only=[l])
        sb_check("old q", t, e0, mode="old", only=[l])
if "C" in part:
    print("Part C: Remark 3 (Lemma P only on S0; old q at S_b \\ S0) with deep poles outside S0")
    for A, v in [(-70, 2**6 * 3**6 * 7 * 11**200), (0, 2**5 * 7 * 3 * 331**60), (-69, 2**8 * 3 * 7 * 337**40 * 17**150)]:
        x = pseudo_x(A, v)
        S = splus(A)
        u = x + max(S) * v
        t1 = Fr(u, v); t2 = Fr(A + 10) - t1
        print(f"A={A} v={L.pari(f'factor({v})')} x={x}")
        sb_check("t1", t1, ELL0, mode="S0only")
        sb_check("t2", t2, ELL0, mode="S0only")
