"""tyz-35: numerical check of the HUMAN CHECK item (a) of the leaf TYZThm33Pinned (choice of lifts, n = 5 mod 8).

For squarefree n = 5 (mod 8), the conjugates of x = f0(P_n) are the Heegner points phi(tau_Q) of the forms Q of
discriminant -64n with 32 | A, B = -8 (mod 64), one per class of Pic(Z[4 sqrt -n]) (tyz-t1 heeg.py). Two lifts
to Gal(Qbar/Q) of the same class of Cl(K_n) act on H_{n,4} by classes t, t' in the same fibre of
Pic(O_{n,4}) -> Cl(O_K). The leaf's `forall f` form is a consequence of TYZ Thm 3.3 iff z_n^t - z_n^{t'} is
torsion for all such t, t', i.e. (z_n^t = (1 - psi(t) i) x^t, psi constant on fibres) iff x^t - x^{t'} is torsion.
This script computes the fibres exactly (O4-ideal of Q extended to O_K, reduced form of disc -4n) and checks
16 (phi(tau_Q) - phi(tau_Q')) in Lambda for all Q, Q' in one fibre.
Usage: python3 fibre5.py n1 n2 ... (sequential)."""
import sys, math
sys.path.insert(0, '.')
from heeg7 import zphi, tau_of, heegner_forms, qfbred, in_lattice, classno


def hnf2(vecs):
    """HNF of the Z-span of integer vectors (u, v) in Z^2 (basis 1, sqrt(-n)): returns (a, b, d) with
    lattice = Z (a, 0) + Z (b, d), 0 <= b < a."""
    # gcd on second coordinate
    vs = [list(v) for v in vecs]
    d = 0; row = None
    g_rows = []
    # reduce: find combination with second coord = gcd
    cur = None
    for v in vs:
        if cur is None: cur = v[:]; continue
        # combine cur and v on second coordinate via extended gcd
        a1, b1 = cur[1], v[1]
        if b1 == 0:
            g_rows.append(v); continue
        if a1 == 0:
            g_rows.append(cur); cur = v[:]; continue
        g, x, y = egcd(a1, b1)
        new = [x * cur[0] + y * v[0], g]
        other = [(b1 // g) * cur[0] - (a1 // g) * v[0], 0]
        g_rows.append(other); cur = new
    d = cur[1]
    if d < 0: cur = [-cur[0], -cur[1]]; d = -d
    a = 0
    for r in g_rows:
        assert r[1] % d == 0 if d else True
        r0 = r[0] - (r[1] // d) * cur[0] if d else r[0]
        a = math.gcd(a, r0)
    b = cur[0] % a
    return a, b, d


def egcd(a, b):
    if b == 0: return (abs(a), (1 if a > 0 else -1), 0)
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y


def image_class(Q, n):
    A, B, C = Q
    # O4-ideal: A Z + (-B/2 + 4 sqrt(-n)) Z ; generators of A O_K, beta O_K with O_K = Z[sqrt(-n)] (n = 1 mod 4)
    b0, b1 = -B // 2, 4
    vecs = [(A, 0), (0, A), (b0, b1), (-n * b1, b0)]   # beta * sqrt(-n) = -n b1 + b0 sqrt(-n)
    a, b, d = hnf2(vecs)
    # ideal = d * (a/d Z + (b/d + sqrt(-n)) Z) up to content; primitive part
    assert a % d == 0 and b % d == 0, (Q, a, b, d)
    a1, b1_ = a // d, b // d
    assert (b1_ * b1_ + n) % a1 == 0
    return qfbred(a1, 2 * b1_, (b1_ * b1_ + n) // a1)


def run(n):
    reps = heegner_forms(-64 * n, -8)
    fib = {}
    for Q in reps.values():
        fib.setdefault(image_class(Q, n), []).append(Q)
    h = classno(-4 * n)
    sizes = sorted(set(len(v) for v in fib.values()))
    bad = 0; checks = 0
    for key, L in fib.items():
        z0 = zphi(tau_of(*L[0]))
        for Q in L[1:]:
            checks += 1
            ok = in_lattice(16 * (zphi(tau_of(*Q)) - z0))
            bad += not ok
    keys = list(fib)
    ctrl = sum(in_lattice(16 * (zphi(tau_of(*fib[keys[i]][0])) - zphi(tau_of(*fib[keys[j]][0]))))
               for i in range(len(keys)) for j in range(i + 1, len(keys)))
    print("n=%d: h(-4n)=%d, #fibres=%d, fibre sizes %s, pairs checked %d, non-torsion differences %d;"
          " control (different fibres) torsion differences %d of %d"
          % (n, h, len(fib), sizes, checks, bad, ctrl, len(keys) * (len(keys) - 1) // 2)); sys.stdout.flush()
    return bad


if __name__ == "__main__":
    tot = 0
    for a in sys.argv[1:]: tot += run(int(a))
    print("total non-torsion differences:", tot)
