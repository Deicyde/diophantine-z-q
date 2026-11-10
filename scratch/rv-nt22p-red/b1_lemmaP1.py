"""Batch 1: Lemma P(1)-(2) locally.  For t = u/v with l^e || v, check v_l(R0) = 2e,
v_l(t-1) = -e, and whether R0 is a square in Q_l; then build q0 = w/l^e and check
v_l(1 - R0 q0^2) >= N.  30 inputs, plus controls with F(t) < 0 (eta = -1)."""
import random
from fractions import Fraction as Fr
import slopelib as L

rng = random.Random(20261109)

def rand_u(v, lo, hi):
    while True:
        u = rng.randint(lo * v, hi * v)
        if L.math.gcd(u, v) == 1 and Fr(u, v) not in [Fr(c) for c in L.CSET + [1]]:
            return u

inputs = []   # (label, l, e, u, v, eta)
for e in [1, 2, 3, 4, 5]:
    v = 2 ** e * 7 ** 3            # extra prime 7 to the third, not used
    u = rand_u(v, 2, 50)
    inputs.append((f"l=2 e={e}", 2, e, u, v, 1))
for l in [3, 5, 7, 13]:
    for e in [1, 5, 40]:
        v = l ** e * 11
        u = rand_u(v, 2, 50)
        inputs.append((f"l={l} e={e}", l, e, u, v, 1))
for l, e in [(11, 2), (331, 2), (317, 6)]:
    v = l ** e
    u = rand_u(v, 2, 50)
    inputs.append((f"l={l} e={e} (S_b not S0)", l, e, u, v, 1))
# several primes at once (checked at each)
v = 2 ** 7 * 3 ** 6 * 5 ** 5 * 7 ** 5 * 13 ** 5
u = rand_u(v, 2, 50)
for l in [2, 3, 5, 7, 13]:
    inputs.append((f"multi, at l={l}", l, L.vp_int(v, l), u, v, 1))
# controls F(t) < 0, eta = -1
for l, e in [(2, 5), (3, 5), (5, 5), (7, 5), (13, 5)]:
    v = l ** e
    while True:
        u = rng.randint(-14 * v, -1 * v)
        if L.math.gcd(u, v) == 1 and L.F(Fr(u, v)) < 0:
            break
    inputs.append((f"CONTROL F<0 l={l} e={e}", l, e, u, v, -1))
assert len(inputs) == 30, len(inputs)

print("label | v_l(R0) | v_l(t-1) | R0 square in Q_l | v_l(1-R0 q0^2) >= N")
fails = []
for lab, l, e, u, v, eta in inputs:
    t = Fr(u, v)
    R0 = L.R0_of(t, eta)
    assert R0 > 0
    vR0, vt1 = L.vp(R0, l), L.vp(t - 1, l)
    sq = L.is_square_Ql(R0, l)
    N = 23 * e + L.vp_int(12, l) + 2
    ok2 = None
    if sq:
        U = R0 / Fr(l) ** vR0
        w = L.unit_sqrt_mod(U, l, N + 5)
        q0 = Fr(w, l ** e)
        ok2 = L.vp(1 - R0 * q0 * q0, l) >= N
    hyp = L.lemmaP_hyp(t, l) if eta == 1 else False
    print(f"{lab:28s} | {vR0:4d} | {vt1:4d} | {sq!s:5s} | {ok2} | LemmaP hyp {hyp}")
    if hyp and (vR0 != 2 * e or vt1 != -e or not sq or not ok2):
        fails.append(lab)
print("FAILURES of Lemma P(1)-(2) under its hypotheses:", fails)

# statistics: fraction of squares for l = 2, e = 1, 2 (eta = 1), and for eta = -1 at each l
print("\nstatistics over 2000 random u each:")
for l, e, eta in [(2, 1, 1), (2, 2, 1), (2, 3, 1), (3, 1, 1), (2, 5, -1), (3, 5, -1), (5, 5, -1), (7, 5, -1), (13, 5, -1)]:
    v = l ** e; n = sq = 0
    while n < 2000:
        u = rng.randint(-10**6, 10**6)
        if L.math.gcd(u, v) != 1:
            continue
        t = Fr(u, v)
        Ft = L.F(t)
        if Ft == 0 or (Ft > 0) != (eta == 1):
            continue
        n += 1
        sq += L.is_square_Ql(L.R0_of(t, eta), l)
    print(f"  l={l} e={e} eta={eta}: R0 square in {sq}/{n}")
