"""Check of the 2-adic step of Proposition A(i): for theta = 1 (mod 8) and every odd beta, the
quartic N^2 = beta (M^4 - theta^2 e^4) has a 2-adic point.  We search M, e < 64 and test whether
beta (M^4 - theta^2 e^4) is a nonzero 2-adic square (odd part = 1 mod 8, even valuation)."""
def is_sq2(x):
    if x <= 0 and x != 0:
        pass
    if x == 0:
        return False
    v = 0
    while x % 2 == 0:
        x //= 2; v += 1
    return v % 2 == 0 and x % 8 == 1
ok = True
for theta in [1, 9, 17, 25, 33, 41, 49, 57, 73, 89, 97, 113]:
    for beta in [1, 3, 5, 7, -1, -3, -5, -7, 2, 6, 10, 14, -2, -6, -10, -14]:
        found = any(is_sq2(beta * (M ** 4 - theta ** 2 * e ** 4))
                    for M in range(0, 64) for e in range(0, 64) if (M, e) != (0, 0))
        if not found:
            ok = False
            print("no 2-adic point found", theta, beta)
print("all (theta, beta) pairs have a 2-adic point:", ok)
