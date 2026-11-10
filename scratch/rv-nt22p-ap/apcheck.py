# Independent check of Proposition AP (nt-22p section 3.3): indexing, signs, field 1, valuations,
# and the local-square condition of Lemma P(1) on the two variable slopes.
import random, sys
from fractions import Fraction as Fr

C = [0, -15, -20, -24, -30, -60]
T = C + [1]
S0 = [2, 3, 5, 7, 13]
B = lambda l: 4          # every prime of S0 is <= 324, so B_l = 4

def F(t):
    r = Fr(1)
    for c in C: r *= (t - c)
    return r

def vint(l, n):
    n = abs(n); assert n
    k = 0
    while n % l == 0: n //= l; k += 1
    return k

def vrat(l, q): return vint(l, q.numerator) - vint(l, q.denominator)

def unit_part(l, q):
    e = vrat(l, q); q = q / Fr(l) ** e
    return q.numerator * pow(q.denominator, -1, l ** 3) % l ** 3

def is_local_square(l, q):
    # q in Q_l^x is a square iff v_l(q) even and the unit part is a square (mod l, or mod 8 for l=2)
    if vrat(l, q) % 2: return False
    u = unit_part(l, q)
    if l == 2: return u % 8 == 1
    return pow(u % l, (l - 1) // 2, l) == 1

def S_plus(Ap): return sorted(set(T) | {Ap - c for c in T})

def check(A, x, v):
    Ap = A + 10
    S = S_plus(Ap); M, m = max(S), min(S); K = M - m
    # closed form of K_A
    assert K == (Ap + 120 if Ap >= -59 else 2 - Ap), (A, K)
    u = x + M * v
    terms = [x + j * v for j in range(K + 1)]
    for c in S:
        assert u - c * v in terms and 0 <= M - c <= K
    t1 = Fr(u, v); t2 = Ap - t1; t3 = Fr(-10)
    assert t1 + t2 + t3 == A
    # field 1
    for t in (t1, t2):
        assert t not in C and t != 1
    # signs
    assert F(t1) > 0 and F(t2) > 0, (A, x, v)
    assert t2 < -60
    # numerators of t2 - c are -(u - (A'-c) v)
    u2 = Ap * v - u
    for c in T:
        assert u2 - c * v == -(u - (Ap - c) * v)
    out = []
    for l in S0:
        e = vint(l, v)
        for (t, num) in ((t1, u), (t2, u2)):
            R0 = F(t) / (t - 1) ** 8
            assert vrat(l, t - 1) == -e
            assert vrat(l, R0) == 2 * e
            field2 = e <= B(l) and 2 * e <= 8 * B(l)
            if not field2:
                assert e >= 2 and (l != 2 or e >= 5)
                sq = is_local_square(l, R0)
                out.append((l, e, sq))
                assert sq, (A, x, v, l, e)
    return out

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
P = 2 * 3 * 5 * 7 * 13
As = list(range(-80, 61)) + [-10**6, -1000, -71, -70, -69, -68, 1000, 10**6]
nlp = 0
for A in As:
    for _ in range(3):
        v = 1
        for l in S0: v *= l ** random.randint(1, 30)
        v *= random.choice([1, 11, 17 * 19, 331])
        x = P * random.randint(1, 10**12) + 1       # all terms = x mod each l in S0: l-units
        res = check(A, x, v)
        nlp += len(res)
print('Prop AP checks passed for', len(As), 'values of A x 3 samples;', nlp, 'Lemma-P cases, all local squares')
# control: eta = -1 slopes (F(t) < 0) and l=2 with e <= 2 are not always squares
bad = 0
for _ in range(200):
    v = 2 ** random.randint(1, 2) * random.choice([3, 5, 7]); x = random.randrange(1, 10**9, 2)
    t = Fr(x + v, v)
    if F(t) > 0 and not is_local_square(2, F(t) / (t - 1) ** 8): bad += 1
print('control l=2, e<=2: non-squares in', bad, 'of 200')
