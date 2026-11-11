# Adversarial test of el-cert X3b's independence model: for real test-site data (k0.py, Lean
# formulas), factor num(Theta0) (Theta0 = poleTheta with R0 inside W, i.e. M1) by trial division
# up to 2e6 and record the Legendre symbol (R0/p) at primes p > 13 with p not dividing R0.
import sys; sys.path.insert(0, "scratch/el-qfree")
import cypari2; pari = cypari2.Pari()
from fractions import Fraction as Fr
import k0
cases = [(n, 1, h, s0) for n in (1, 2, 3) for (h, s0) in ((2, 3), (3, 5), (2, 7), (5, 2))]
tot_m = tot_p = 0
for (n, kap, h, s0) in cases[:12]:
    t = Fr(n); C = k0.testC(n, kap, t, h, s0)
    if any(c.iszero() for c in C) and False: pass
    R0 = k0.testR0(1, t)
    Th = k0.theta(R0, C)
    if Th is None or Th == 0: print(n, h, s0, "Theta0 degenerate"); continue
    N = abs(Th.numerator)
    fa = pari.factor(N, 2*10**6)
    ps = [int(fa[0][i]) for i in range(len(fa[0])) if pari.isprime(fa[0][i]) and int(fa[0][i]) > 13
          and int(fa[0][i]) < 2*10**6]
    syms = [int(pari.kronecker(R0.numerator * R0.denominator, p)) for p in ps if R0.numerator % p and R0.denominator % p]
    mneg = syms.count(-1); tot_m += mneg; tot_p += len(syms)
    print(f"n={n} h={h} s0={s0} digits(num Theta0)={len(str(N))} small primes={ps} (R0/p)={syms}")
print("total (R0/p) = -1:", tot_m, "of", tot_p)

# Per instance: which signed divisors m of 2730 satisfy (-m/p) = -1 at every obstruction prime found
from itertools import combinations
divs = sorted({s*d for d in range(1, 2731) if 2730 % d == 0 for s in (1, -1)})
print("signed divisors of 2730:", len(divs))
for (n, kap, h, s0) in cases[:12]:
    t = Fr(n); C = k0.testC(n, kap, t, h, s0); R0 = k0.testR0(1, t); Th = k0.theta(R0, C)
    N = abs(Th.numerator); fa = pari.factor(N, 2*10**6)
    obs = [int(fa[0][i]) for i in range(len(fa[0])) if 13 < int(fa[0][i]) < 2*10**6 and pari.isprime(fa[0][i])
           and R0.numerator % int(fa[0][i]) and int(pari.kronecker(R0.numerator*R0.denominator, int(fa[0][i]))) == -1]
    good = [m for m in divs if all(int(pari.kronecker(-m, p)) == -1 for p in obs)]
    print(f"n={n} h={h} s0={s0} obstruction primes={obs} surviving m: {len(good)}/{len(divs)}")
