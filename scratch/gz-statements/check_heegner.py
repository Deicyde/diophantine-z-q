# Check: for odd negative fundamental D (D%4==1, squarefree) and N with every prime p|N
# satisfying jacobi(p,|D|)=1 (Lean HeegnerHyp), D is a square mod 4N (Gross-Zagier's form),
# and (D,N)=1, and kronecker(D,p)=1 (p splits). Sample of 30 pairs, levels 32 d^2 (d = 5 mod 8
# squarefree) and a few odd/non-squarefree levels.
from sympy import factorint, jacobi_symbol
def sqfree(n): return all(e == 1 for e in factorint(abs(n)).values())
def kron(D, p):
    if p == 2:
        return 0 if D % 2 == 0 else (1 if D % 8 in (1, 7) else -1)
    return jacobi_symbol(D % p, p)
def heeg(N, D): return all(jacobi_symbol(p, -D) == 1 for p in factorint(N))
def sq_mod(D, m): return any((b * b - D) % m == 0 for b in range(m))
levels = [32 * d * d for d in (5, 13, 21, 29, 37)] + [11, 37, 43, 9 * 7, 27, 49 * 3]
out = []
for N in levels:
    found = 0
    D = -7
    while found < 3 and D > -20000:
        if D % 4 == 1 and sqfree(D) and heeg(N, D):
            from math import gcd
            ok = sq_mod(D, 4 * N) and gcd(D, N) == 1 and all(kron(D, p) == 1 for p in factorint(N))
            out.append((N, D, ok))
            found += 1
        D -= 1
    if len(out) >= 30: break
out = out[:30]
for r in out: print(*r)
print("pairs", len(out), "failures", sum(1 for r in out if not r[2]))
