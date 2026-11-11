# X3b: probability that the M1 theta=1 curve is locally obstructed for EVERY multiplier m in a set,
# from obstruction primes p | num(Theta0) with (R0/p) = -1 (criterion X3a: need (-m/p) = -1).
# Model: number of obstruction primes r ~ Poisson(lam), lam = (1/2) log log N, N = num(Theta0);
# the primes are random primes ~1e12 with (R0/p) = -1, R0 = 2730^6 F(n) (n = 7).
import random, math, cypari2
pari = cypari2.Pari(); random.seed(3)
def F(n): return n*(n+15)*(n+20)*(n+24)*(n+30)*(n+60)
R0 = 2730**6 * F(7)
small = [int(x) for x in pari('primes([2,324])')]          # 66 primes
gens = [-1] + small                                          # 67 generators
def leg(a, p): return int(pari.kronecker(a, p))
def rand_obst_prime():
    while True:
        p = int(pari.nextprime(random.randint(10**12, 2*10**12)))
        if leg(R0, p) == -1: return p
def poisson(lam):
    L, k, prod = math.exp(-lam), 0, random.random()
    while prod > L: k += 1; prod *= random.random()
    return k
S8 = [f*m0 for f in (1, 2) for m0 in (1, 3, 5, 7)]           # DL's multipliers
S64 = [s*d for s in (1, -1) for d in [x for x in range(1, 2731) if 2730 % x == 0]]
def ok_set(S, ps): return any(all(leg(-m, p) == -1 for p in ps) for m in S)
def ok_group(ps):
    # need m = prod gens^e with (-m/p) = -1 for all p: affine system over F2 in e (67 unknowns)
    if not ps: return True
    rows = []
    for p in ps:
        c = [0 if leg(g, p) == 1 else 1 for g in gens]          # character of each generator
        rhs = (1 + (0 if leg(-1, p) == 1 else 1)) % 2            # (-1)^e.(-1/p) chars: want sum = 1+[-1/p]
        rows.append(c + [rhs])
    M = pari.matrix(len(rows), 68, [x for r in rows for x in r]) * pari.Mod(1, 2)
    A = M[:, :67] if False else pari('(M)->M[,1..67]')(M); b = pari('(M)->M[,68]')(M)
    try: pari.matsolve(A, b) if False else pari('(A,b)->matsolvemod(lift(A),2,lift(b))')(A, b)
    except Exception: return False
    return pari('(A,b)->type(matsolvemod(lift(A),2,lift(b)))!="t_INT"')(A, b) == 1
for logN in (10**3, 10**6, 10**9):
    lam = 0.5 * math.log(logN * math.log(10))
    trials = 200; c8 = c64 = cg = 0
    for _ in range(trials):
        ps = [rand_obst_prime() for _ in range(poisson(lam))]
        c8 += ok_set(S8, ps); c64 += ok_set(S64, ps); cg += ok_group(ps)
    print(f"log10 N = {logN:>10}: lam = {lam:.1f}; P(some m locally ok): DL8 {c8/trials:.3f}, "
          f"2730-signed64 {c64/trials:.3f}, 2^67 group {cg/trials:.3f}")
