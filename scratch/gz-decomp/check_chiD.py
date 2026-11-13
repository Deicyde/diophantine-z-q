# gz-decomp: check that chiD D n = jacobi(n, |D|) equals the Kronecker symbol (D/n), and that
# HeegnerHyp's clause jacobi(p, |D|) = 1 at p = 2 is "D = 1 mod 8", for odd fundamental D < 0.
# Pure Python (PARI is not available on this host: ~/pyenv is missing, no network).
def jacobi(a, n):
    assert n > 0 and n % 2 == 1
    a %= n; r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: r = -r
        a %= n
    return r if n == 1 else 0
def kronecker(D, n):
    # Kronecker symbol (D/n), n >= 1
    r = 1
    while n % 2 == 0:
        n //= 2
        if D % 2 == 0: return 0
        if D % 8 in (3, 5): r = -r
    return r * jacobi(D, n) if n > 1 else r
def sqfree(m):
    m = abs(m); p = 2
    while p * p <= m:
        if m % (p * p) == 0: return False
        p += 1
    return True
Ds = [D for D in range(-5, -200, -1) if D % 4 == 1 and sqfree(D)][:30]
bad = 0; tested = 0
for D in Ds:
    for n in range(1, 201):
        tested += 1
        if jacobi(n, abs(D)) != kronecker(D, n): bad += 1
    if (jacobi(2, abs(D)) == 1) != (D % 8 == 1): bad += 1
print(f"{len(Ds)} discriminants D in [-199,-7], n in 1..200: {tested} pairs, {bad} mismatches")
