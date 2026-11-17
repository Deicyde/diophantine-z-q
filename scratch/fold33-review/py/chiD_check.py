# fold33-review: GZDecomp.chiD D n = jacobiSym n |D| agrees with the Kronecker symbol (D/n) (the character of Q(sqrt D))
# for odd negative fundamental D = 1 mod 4.  30 (D, n) pairs, plain Python (no sympy on this host).
import random
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
def kron(D, n):
    # Kronecker symbol (D/n), n >= 1
    r = 1
    while n % 2 == 0:
        n //= 2
        if D % 2 == 0: return 0
        r *= 1 if D % 8 in (1, 7) else -1
    return r * (jacobi(D, n) if n > 1 else 1)
def sqfree(m):
    m = abs(m); p = 2
    while p * p <= m:
        if m % (p * p) == 0: return False
        p += 1
    return True
random.seed(33)
Ds = [D for D in range(-5, -400, -1) if D % 4 == 1 and sqfree(D)]
bad = 0
for i in range(30):
    D = random.choice(Ds); n = random.randint(1, 500)
    a, b = jacobi(n, -D), kron(D, n)
    bad += a != b
    print(D, n, a, b)
print("mismatches:", bad)
