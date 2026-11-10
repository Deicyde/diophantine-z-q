"""Batch 2: the pole input B for slopes with poles at old primes, with the modified choice of q
(Lemma P ball at S_pole, v_p(q) >= C_p elsewhere on S_b) and negative controls with the old
choice.  Reports v_l(B) at every prime of S0 and at the pole primes, parity at the other primes
of the model S_b, the S_b-part of the reduced denominator, and 0 < B < 1/2.
Selected (contact) primes are not modelled here (random test values in every group); they are
treated in batch 3."""
import random, time, math, sys
from fractions import Fraction as Fr
import slopelib as L

rng = random.Random(7)
H = [331, 337]
Sb = L.S_HT + H
ELL0 = L.ell0(H)

def rand_u(v, lo, hi, sign=1):
    while True:
        u = rng.randint(lo * v, hi * v)
        t = Fr(u, v)
        if math.gcd(u, v) == 1 and t != 1 and L.F(t) != 0 and (L.F(t) > 0) == (sign > 0):
            return u

# (label, v, mode, sign) ; mode: 'new' = modified choice, 'old' = v_p(q) >= C_p everywhere,
# 'newP2' = Lemma P branch forced also where field 2 holds (l=2, e=3,4)
inputs = []
for e in [1, 2, 3, 4, 5]:
    inputs.append((f"l=2 e={e}", 2 ** e, "new", 1))
for l in [3, 5, 7, 13]:
    for e in [5, 200]:
        inputs.append((f"l={l} e={e}", l ** e, "new", 1))
inputs.append(("l=331(H) e=2", 331 ** 2, "new", 1))
inputs.append(("l=331(H) e=40", 331 ** 40, "new", 1))
inputs.append(("l=11 e=200", 11 ** 200, "new", 1))
inputs.append(("multi 2^7 3^6 5^5 7^5 13^5", 2**7 * 3**6 * 5**5 * 7**5 * 13**5, "new", 1))
inputs.append(("multi 2^150 3^130 5^140 7^5 13^200 331^3", 2**150 * 3**130 * 5**140 * 7**5 * 13**200 * 331**3, "new", 1))
inputs.append(("l=2 e=3 Lemma P branch", 2 ** 3, "newP2", 1))
inputs.append(("l=2 e=4 Lemma P branch", 2 ** 4, "newP2", 1))
inputs.append(("CONTROL old q, l=3 e=200", 3 ** 200, "old", 1))
inputs.append(("CONTROL old q, l=13 e=200", 13 ** 200, "old", 1))
inputs.append(("CONTROL old q, l=2 e=200", 2 ** 200, "old", 1))
inputs.append(("CONTROL F<0, l=3 e=200, old q", 3 ** 200, "old", -1))
inputs.append(("F<0, l=5 e=200, ball (eta=-1)", 5 ** 200, "newneg", -1))
for e in [120, 130, 140, 150, 160]:
    inputs.append((f"threshold old q, l=3 e={e}", 3 ** e, "old", 1))
assert len(inputs) == 30, len(inputs)

summary = []
for lab, v, mode, sign in inputs:
    T0 = time.time()
    u = rand_u(v, 2, 60, sign) if sign > 0 else rand_u(v, -14, -1, sign)
    t = Fr(u, v)
    eta = 1 if L.F(t) > 0 else -1
    D = L.model_tests([], rng)
    R0 = L.R0_of(t, eta)
    # largest |C| in the real embeddings (for the size of the auxiliary power)
    Dmax = max(abs(x) + 1.5 * abs(y) for row in D for (x, y) in row) + 1
    Cmax = max(math.log10(Dmax) - k * math.log10(abs(float(R0))) - (k + 1) * math.log10(abs(float(t - 1))) for k in (1, 25))
    if mode == "old":
        Spole = []
    elif mode == "newneg":
        Spole = [l for l in Sb if L.vp_int(v, l) > 0 and not L.field2_holds(t, l)]
    elif mode == "newP2":
        Spole = [l for l in Sb if L.vp_int(v, l) > 0 and L.lemmaP_hyp(t, l)]
    else:
        Spole = [l for l in Sb if not L.field2_holds(t, l) and L.lemmaP_hyp(t, l)]
        bad = [l for l in Sb if not L.field2_holds(t, l) and not L.lemmaP_hyp(t, l)]
        assert not bad, (lab, bad)
    Nl = {l: 23 * L.vp_int(v, l) + L.vp_int(12, l) + 2 for l in Spole}
    q, info = L.choose_q(t, eta, Sb, Spole, Nl, [], [], ELL0, Cmax_log10=Cmax)
    P = L.PoleInput(t, eta, q, ELL0, D)
    check = sorted(set(L.S0) | {l for l in Sb if L.vp_int(v, l) > 0} | {l for l in Sb if L.vp(R0, l) % 2})
    out = {}
    for l in check:
        r = P.local(l)
        out[l] = (r["vB"], P.v_a(l), r["ok"])
    # parity at all primes of the model S_b (v_p(B) == v_p(R0) mod 2 identically; check directly)
    odd_neg = []
    for l in Sb:
        if l in out:
            vb = out[l][0]
        else:
            vb = P.local(l)["vB"]
        if vb is None or (vb < 0 and vb % 2):
            odd_neg.append((l, vb))
    rl = P.real()
    S0ok = all(out[l][0] is not None and out[l][0] >= 4 for l in L.S0)
    Bok = 0 < rl["B"] < 0.5
    den_Sb = [(l, -out[l][0]) for l in out if out[l][0] is not None and out[l][0] < 0]
    line = (f"{lab:42s} eta={eta:+d} Spole={Spole} | S0 v(B)>=4: {S0ok} | "
            f"v_l(B) at check primes: {{{', '.join(f'{l}:{out[l][0]}' for l in check)}}} | "
            f"odd negative on S_b: {odd_neg} | S_b-part of den(B): {den_Sb} | 0<B<1/2: {Bok} "
            f"(B={mpf_s(rl['B']) if False else float(rl['B']) if rl['B'] > 1e-300 else 'tiny'}) | {time.time()-T0:.1f}s")
    print(line, flush=True)
    summary.append((lab, S0ok and Bok and not odd_neg))
print("\nSUMMARY (True = all PC hypotheses checked at S_b and real place):")
for lab, ok in summary:
    print(f"  {lab:42s} {ok}")
