"""Differential check (pure Python; PARI/cypari2 and sympy are not installed on this host).
(a) The Lean definition of `kroneckerSym D n` (BFHPrinted/Kronecker.lean), transcribed: product over
    p^k || n of (chi_8(D) if p = 2 else Legendre(D, p) by Euler's criterion)^k, (D/0) = [|D| = 1].
(b) An independent implementation of the Kronecker symbol: Cohen, A Course in Computational Algebraic
    Number Theory, Algorithm 1.4.10 (binary Kronecker; number UNVERIFIED), with no factorization.
(c) For D = 1 mod 4, the Jacobi symbol J(n | |D|) (the definition of GZDecomp.chiD), by (b) with
    arguments (n, |D|).
On 30 pairs (D fundamental discriminant, 0 <= n <= 400), run one after another."""
import random

def is_squarefree(m):
    m = abs(m); d = 2
    while d * d <= m:
        if m % (d * d) == 0:
            return False
        d += 1
    return True

def is_fundamental(D):  # Mathlib's Int.IsFundamentalDiscr, via isFundamentalDiscr_iff_squarefree
    if D % 4 == 1:
        return is_squarefree(D)
    if D % 4 == 0:
        m = D // 4
        return is_squarefree(m) and m % 4 in (2, 3)
    return False

def factor(n):
    out, p = [], 2
    while p * p <= n:
        k = 0
        while n % p == 0:
            n //= p; k += 1
        if k:
            out.append((p, k))
        p += 1
    if n > 1:
        out.append((n, 1))
    return out

def chi8(D):
    r = D % 8
    return 0 if r % 2 == 0 else (1 if r in (1, 7) else -1)

def legendre(a, p):  # Euler's criterion
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def kronecker_lean(D, n):  # (a)
    if n == 0:
        return 1 if abs(D) == 1 else 0
    r = 1
    for p, k in factor(n):
        r *= (chi8(D) if p == 2 else legendre(D, p)) ** k
    return r

def kronecker_cohen(a, b):  # (b), Cohen Alg. 1.4.10, for b >= 0
    if b == 0:
        return 1 if abs(a) == 1 else 0
    if a % 2 == 0 and b % 2 == 0:
        return 0
    tab2 = [0, 1, 0, -1, 0, -1, 0, 1]
    v = 0
    while b % 2 == 0:
        v += 1; b //= 2
    k = 1 if v % 2 == 0 else tab2[a & 7]
    if b < 0:  # not reached (b >= 0)
        b = -b
    while True:
        if a == 0:
            return k if b == 1 else 0
        v = 0
        while a % 2 == 0:
            v += 1; a //= 2
        if v % 2 == 1:
            k *= tab2[b & 7]
        if a & b & 2:
            k = -k
        r = abs(a); a = b % r; b = r

random.seed(20261116)
fund = [D for D in range(-200, 201) if D != 1 and is_fundamental(D)]
bad = 0
for _ in range(30):
    D, n = random.choice(fund), random.randint(0, 400)
    a, b = kronecker_lean(D, n), kronecker_cohen(D, n)
    line = f"D={D:5d} n={n:4d} lean_def={a:2d} cohen={b:2d}" + ("" if a == b else "  MISMATCH")
    bad += (a != b)
    if D % 4 == 1 and n != 0:
        j = kronecker_cohen(n, abs(D))
        line += f"  J(n||D|)={j:2d}" + ("" if j == a else "  MISMATCH-J")
        bad += (j != a)
    print(line)
print("mismatches:", bad)
