"""C2. A catalogue-free choice of the initial progression for the twenty-two forms of
Proposition 6.2.

T = (u1, u2, v) in r0 + W0 Z^3 with
  r0 = (rho, rho, 8 P_s omega),  W0 = 2^9 P_s^2 (so 2^10 and q^2 divide W0),
  rho, omega = 1 mod 16, = 3 mod 7, = 1 mod q for the other odd q <= 324.
On the real box u1, u2 in (X, 2X), 0 < v < X / (2(|A| + 62)) the signs are
eps = +1 for v and the forms with j = 1, 2, and -1 for j = 3.

Checked exactly, for every form nu and every A in the sample:
  (1) k_nu := S_ht-part of F_nu(r0) divides P_s^4 (no catalogue prime);
  (2) W0 * (every coefficient of F_nu) / k_nu is divisible by 8 * prod_{odd q <= 324} q,
      so k_nu and Psi_nu mod 8 and mod q are constant on the whole progression;
  (3) Psi_nu(r0) = eps F_nu(r0) / k_nu is = 1 mod 8, a non-residue mod 7, and
      not 0 or -1 mod every odd q <= 324;
  (4) the same on 30 random points of the progression, by direct factorization.
"""
import random
from functools import reduce

def primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p ** .5) + 1))]

SMALL = primes_upto(324)
PS = reduce(lambda a, b: a * b, SMALL)
ODD = [q for q in SMALL if q > 2]
Q8 = 8 * reduce(lambda a, b: a * b, ODD)
B = [0, -15, -20, -24, -30, -60, 1]

def crt(residues):
    x, m = 0, 1
    for r, n in residues:
        t = (r - x) * pow(m, -1, n) % n
        x, m = x + m * t, m * n
    return x % m

target = [(1, 16), (3, 7)] + [(1, q) for q in ODD if q != 7]
rho = crt(target)
omega = rho
W0 = 2 ** 9 * PS ** 2
r0 = (rho, rho, 8 * PS * omega)

def forms(A):
    """(label, coefficient vector on (u1, u2, v), sign on the box)."""
    out = [("v", (0, 0, 1), 1)]
    for b in B:
        out.append((f"u1-({b})v", (1, 0, -b), 1))
        out.append((f"u2-({b})v", (0, 1, -b), 1))
        out.append((f"u3-({b})v", (-1, -1, A - b), -1))
    return out

def sht_part(x):
    x, d = abs(x), 1
    for q in SMALL:
        while x % q == 0:
            x //= q; d *= q
    return d

def check_unit(psi):
    if psi % 8 != 1:
        return "mod 8"
    if psi % 7 not in (3, 5, 6):
        return "mod 7"
    for q in ODD:
        if psi % q in (0, q - 1):
            return f"mod {q}"
    return None

def run(A, rng, npts=30):
    fs = forms(A)
    for label, c, eps in fs:
        val = c[0] * r0[0] + c[1] * r0[1] + c[2] * r0[2]
        k = sht_part(val)
        assert (PS ** 4) % k == 0, (A, label, "k does not divide P_s^4")
        for ci in c:
            assert (W0 * ci) % (k * Q8) == 0, (A, label, "coefficient")
        err = check_unit(eps * val // k)
        assert err is None, (A, label, err)
    N = 4 * (abs(A) + 62) * 1000          # box scale X = W0 * N
    for _ in range(npts):
        n = [rng.randrange(N, 2 * N), rng.randrange(N, 2 * N), rng.randrange(0, N // (2 * (abs(A) + 62)) - 1)]
        T = [r0[i] + W0 * n[i] for i in range(3)]
        for label, c, eps in fs:
            val = c[0] * T[0] + c[1] * T[1] + c[2] * T[2]
            assert eps * val > 0, (A, label, "sign")
            k = sht_part(val)
            assert (PS ** 4) % k == 0
            err = check_unit(eps * val // k)
            assert err is None, (A, label, T, err)
    return True

if __name__ == "__main__":
    rng = random.Random(1)
    sample = [0, 1, -1, 2, -2, 7, 60, -60, 61, -61, 324, 10 ** 6, -10 ** 6, 3 ** 40]
    sample += [rng.randrange(-10 ** 30, 10 ** 30) for _ in range(30 - len(sample))]
    for A in sample:
        run(A, rng)
    print(f"all checks passed for {len(sample)} values of A; P_s has {PS.bit_length()} bits")
    print("multipliers k_nu used:", sorted({sht_part(c[0]*r0[0]+c[1]*r0[1]+c[2]*r0[2]) for _, c, _ in forms(0)}, key=lambda k: k.bit_length())[:3], "...")
