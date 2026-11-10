"""The witness a = 1 - R0 q^2 absorbs a pole of the slope at an old prime.
For t = u/v with u - c v (c in C) and u - v units at l, eta = +1 (F(t) > 0) and l^e || v
(e >= 1 for odd l, e >= 3 for l = 2), R0 = v^2 F(u,v)/(u-v)^8 should be a square in Q_l.
We test this on 30 random samples and, for each, build q in Q with v_l(1 - R0 q^2) >= target
at every l in S0 = {2,3,5,7,13} dividing v, q close to R0^(-1/2) in R, and check the result."""
import cypari2, random
from fractions import Fraction
pari = cypari2.Pari()
C = [0, -15, -20, -24, -30, -60]
S0 = [2, 3, 5, 7, 13]
random.seed(22)
def val(x, l):
    x = Fraction(x)
    if x == 0: return 10**9
    n, d, k = x.numerator, x.denominator, 0
    while n % l == 0: n //= l; k += 1
    while d % l == 0: d //= l; k -= 1
    return k
def is_sq_Ql(x, l):
    x = Fraction(x); k = val(x, l)
    if k % 2: return False
    y = x / Fraction(l)**k
    m = 8 if l == 2 else l
    r = (y.numerator * pow(y.denominator, -1, m)) % m
    return r == 1 if l == 2 else pow(r, (l-1)//2, l) == 1
ok = 0
for trial in range(30):
    exps = {l: random.randint(1 if l > 2 else 3, 40) for l in S0}
    v = random.randint(1, 10**6)
    for l in S0:
        while v % l == 0: v //= l
    for l in S0: v *= l**exps[l]
    while True:  # u with all u - c v, u - v units at S0 and u/v > 0
        u = v * random.randint(61, 10**3) + random.randint(1, v - 1)
        if all((u - c*v) % l and (u - v) % l for c in C for l in S0): break
    F = 1
    for c in C: F *= (u - c*v)
    R0 = Fraction(v*v*F, (u - v)**8)
    sq = all(is_sq_Ql(R0, l) for l in S0)
    # build q: l-adic approximations of R0^(-1/2), combined by CRT, then a real correction
    target = {l: 25*exps[l] + 10 for l in S0}   # alpha >= e(k-2) + v(12) + ... with k = 25
    mods, res = [], []
    den = 1
    for l in S0: den *= l**(val(R0, l)//2)
    for l in S0:
        e = val(R0, l)                      # = 2 * exps[l]
        y = R0 / Fraction(l)**e             # unit square
        prec = target[l] + 4
        s = pari.sqrt(pari(f"{y.numerator}/{y.denominator} + O({l}^{prec})"))
        s = int(pari.lift(pari.Mod(pari.truncate(s), l**prec)))
        # q = q0 / den must be l^(-e/2) / s, so q0 = (den / l^(e/2)) / s modulo l^prec
        inv = pow(s, -1, l**prec) * (den // l**(e//2)) % l**prec
        mods.append(l**prec); res.append(inv)
    M = 1
    for m in mods: M *= m
    q0 = int(pari.lift(pari.chinese([pari.Mod(r, m) for r, m in zip(res, mods)])))
    # q = (q0 * P^K + M k) / (den * P^K), P = 1009 an auxiliary prime: the grid spacing
    # M / (den P^K) is small, so q can be put close to the real R0^(-1/2) (weak approximation)
    P = 1009; K = M.bit_length() // 9 + 60
    D = den * P**K
    # x = D / sqrt(R0), to integer precision, via integer square roots
    from math import isqrt
    x = isqrt(D*D*R0.denominator // R0.numerator)
    k = (x - q0 * P**K) // M
    q = Fraction(q0 * P**K + M*k, D)
    a = 1 - R0*q*q
    alphas = {l: val(a, l) for l in S0}
    good = sq and all(alphas[l] >= target[l] for l in S0) and a != 0
    ok += good
    if trial < 3 or not good:
        print(trial, {l: exps[l] for l in S0}, "R0 square at S0:", sq, "v_l(a):", alphas,
              "log10|a|:", round((abs(a.numerator).bit_length()-a.denominator.bit_length())*0.30103))
print(f"{ok}/30 samples: R0 is a square in Q_l for all l in S0 and v_l(a) >= 25 e_l + 10")
# control: e_2 in {1,2} or eta = -1 need not give a square
bad = 0
for trial in range(30):
    v = 2 * random.choice([1, 3, 5, 7]) * random.randint(1, 10**4) * 4**random.randint(0, 0)
    v = v if (v // 2) % 2 else v  # v_2(v) = 1 or more; keep only v_2 in {1,2}
    if val(v, 2) > 2: continue
    u = v * random.randint(61, 10**3) + random.choice([1, 3, 5, 7, 9, 11, 13])
    if u % 2 == 0 or (u - v) % 2 == 0: continue
    F = 1
    for c in C: F *= (u - c*v)
    bad += not is_sq_Ql(Fraction(v*v*F, (u - v)**8), 2)
print(f"control (v_2(v) <= 2): {bad} non-squares in Q_2 among the valid samples")
