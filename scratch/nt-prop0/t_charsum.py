# (1) Jacobsthal: S(n) = sum_x chi(x^3 - n x); for p = 1 mod 4, S(n)^2 + S(gn)^2 = 4p (g nonsquare);
#     for p = 3 mod 4, S(n) = 0.  (2) the fibre count N(al,be) over x not in {0,d,-d} satisfies
#     8N >= p - 15 - |S(d^2)|, and N > 0 for p >= 29 (p = 1 mod 4), p >= 19 (p = 3 mod 4).
from t_fp_surj import chi, primes
bad1 = bad2 = 0; minslack = None
for p in primes(600):
    g = next(a for a in range(2, p) if chi(a, p) == -1)
    S = lambda n: sum(chi(x**3 - n*x, p) for x in range(p))
    for n in range(1, min(p, 40)):
        s1, s2 = S(n), S(g*n)
        if p % 4 == 1 and s1*s1 + s2*s2 != 4*p: bad1 += 1
        if p % 4 == 3 and (s1 or s2): bad1 += 1
    if p > 200: continue
    for d in range(1, p):
        s = S(d*d)
        for al in (1, -1):
            for be in (1, -1):
                N = sum(1 for x in range(p) if x not in (0, d, p-d) and chi(x,p) == al
                        and chi(x-d,p) == be and chi(x+d,p) == al*be)
                if 8*N < p - 15 - abs(s): bad2 += 1
                if N == 0 and ((p % 4 == 1 and p >= 29) or (p % 4 == 3 and p >= 19)): bad2 += 1
print("Jacobsthal identity failures:", bad1, " fibre bound failures:", bad2)
