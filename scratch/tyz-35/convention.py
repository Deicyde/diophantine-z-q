"""tyz-35: pure-Python check (no PARI on this host) of the character convention of the leaf
`TYZThm33Pinned` (Lean `pairSet n (n/d1) d1`): for squarefree n = 5, 7 (mod 8), every divisor d1 of n
and every reduced form f of discriminant D (D = -4n for n = 5, D = -n for n = 7), with m an odd value
of f prime to n:
  chi_T(f) := prod_{q in T} (m/q) = Jacobi(m / g),  g = d1 if d1 = 1 (mod 4) else n/d1;
  (A) n = 5: chi_T(f) = Kronecker(disc Q(sqrt d1), m)                (tyz-t1's chi_{d1} <-> K(sqrt d1));
  (B) n = 7: chi_T(f) = Kronecker(D', m), D' = the one of +-d1 that is 1 mod 4 (unramified K(sqrt D')/K);
  (C) n = 7: chi_T = chi_{T^c} (product formula), i.e. Jacobi(m/n) = 1;
  (D) chi_T is a class invariant (two odd values of f give the same sign).
Usage: python3 convention.py"""
import math


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


def kronecker(D, m):   # m odd positive
    return jacobi(D % m, m) if m > 1 else 1


def coredisc(d):
    return d if d % 4 == 1 else 4 * d


def squarefree(n):
    return all(n % (p * p) for p in range(2, int(math.isqrt(n)) + 1))


def forms(D):
    out = []
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a) == 0:
                c = (b * b - D) // (4 * a)
                if c >= a and math.gcd(math.gcd(a, b), c) == 1 and not (b < 0 and (a == c)):
                    out.append((a, b, c))
        a += 1
    return out


def values(f, n, k=3):
    a, b, c = f; vals = []
    for s in range(1, 40):
        for x in range(-s, s + 1):
            for y in (s - abs(x), -(s - abs(x))):
                m = a * x * x + b * x * y + c * y * y
                if m > 0 and m % 2 == 1 and math.gcd(m, n) == 1 and m not in vals:
                    vals.append(m)
                    if len(vals) == k: return vals
    return vals


def check(n):
    D = -4 * n if n % 8 == 5 else -n
    divs = [d for d in range(1, n + 1) if n % d == 0]
    bad = 0; cnt = 0
    for f in forms(D):
        ms = values(f, n)
        for d1 in divs:
            g = d1 if d1 % 4 == 1 else n // d1
            chis = [jacobi(m, g) if g > 1 else 1 for m in ms]
            bad += len(set(chis)) != 1                                   # (D)
            m = ms[0]; chi = chis[0]; cnt += 1
            if n % 8 == 5:
                bad += chi != (1 if d1 == 1 else kronecker(coredisc(d1), m))   # (A)
            else:
                Dp = d1 if d1 % 4 == 1 else -d1
                bad += chi != (1 if Dp == 1 else kronecker(Dp, m))           # (B)
                bad += jacobi(m, n) != 1                                       # (C)
    return bad, cnt


if __name__ == "__main__":
    ns = [n for n in range(5, 1200) if n % 8 in (5, 7) and squarefree(n)]
    sample = [n for n in ns if sum(1 for p in range(3, n + 1, 2) if n % p == 0 and all(p % r for r in range(3, int(math.isqrt(p)) + 1, 2))) >= 2][:15]
    sample += [5, 13, 7, 23, 1105 if 1105 % 8 in (5, 7) else 1155, 1155 % 8 == 3 and 1023 or 1023, 1195, 1191, 4199, 2605, 3315 % 8 == 3 and 3315 or 3315, 2149, 1365 % 8 == 5 and 1365 or 1365, 21, 165]
    sample = [n for n in dict.fromkeys(sample) if n % 8 in (5, 7) and squarefree(n)][:30]
    tot = 0
    for n in sample:
        b, c = check(n)
        tot += b
        print("n=%5d (mod 8 = %d) checks=%4d mismatches=%d" % (n, n % 8, c, b))
    print("total mismatches:", tot, "over", len(sample), "values of n")
