"""mcheck-rc-deep, block 1: the twisted Shapiro/transfer cochain map (H21) and its degree-n form (tex L3219-3250).

Finite model: G = GL2(Z/8), N = SL2(Z/8) (normal, G/N = (Z/8)^x abelian, playing Delta_f),
M = (Z/8)^2 with the natural action rho, theta = det : G -> (Z/8)^x (a character trivial on N),
target action R(g) = theta(g) rho(g).  Representatives r_delta = diag(delta, 1).
Checks: h(gk,d) = h(g,kd) h(k,d); T maps N-cocycles to G-cocycles; d T = T d in degrees 0, 1, 2
on random (non-closed) cochains; degree-0 weighted sum formula.
"""
import random
import itertools

random.seed(7)
MOD = 8
UNITS = [1, 3, 5, 7]


def mul(A, B):
    return ((A[0] * B[0] + A[1] * B[2]) % MOD, (A[0] * B[1] + A[1] * B[3]) % MOD,
            (A[2] * B[0] + A[3] * B[2]) % MOD, (A[2] * B[1] + A[3] * B[3]) % MOD)


def det(A):
    return (A[0] * A[3] - A[1] * A[2]) % MOD


def inv(A):
    d = det(A)
    di = next(u for u in UNITS if (u * d) % MOD == 1)
    return ((A[3] * di) % MOD, (-A[1] * di) % MOD, (-A[2] * di) % MOD, (A[0] * di) % MOD)


def act(A, v):
    return ((A[0] * v[0] + A[1] * v[1]) % MOD, (A[2] * v[0] + A[3] * v[1]) % MOD)


def vadd(v, w):
    return ((v[0] + w[0]) % MOD, (v[1] + w[1]) % MOD)


def vscale(s, v):
    return ((s * v[0]) % MOD, (s * v[1]) % MOD)


ZERO = (0, 0)
G = [A for A in itertools.product(range(MOD), repeat=4) if det(A) in UNITS]
N = [A for A in G if det(A) == 1]
assert len(G) == 1536 and len(N) == 384
Delta = UNITS
r = {d: (d, 0, 0, 1) for d in Delta}


def coset(g, d):  # g . delta in Delta = G/N via det
    return (det(g) * d) % MOD


def h(g, d):
    gd = coset(g, d)
    x = mul(inv(r[gd]), mul(g, r[d]))
    assert det(x) == 1
    return x


theta = det


def R(g, v):
    return vscale(theta(g), act(g, v))


# random cochains on N with values in M
store = {}


def cochain(name):
    def c(*args):
        key = (name,) + args
        if key not in store:
            store[key] = (random.randrange(MOD), random.randrange(MOD))
        return store[key]
    return c


def d_src(c, n):
    def dc(*g):
        assert len(g) == n + 1
        tot = act(g[0], c(*g[1:]))
        for i in range(n):
            gg = g[:i] + (mul(g[i], g[i + 1]),) + g[i + 2:]
            t = c(*gg)
            tot = vadd(tot, vscale((-1) ** (i + 1), t))
        tot = vadd(tot, vscale((-1) ** (n + 1), c(*g[:n])))
        return tot
    return dc


def d_tgt(c, n):
    def dc(*g):
        tot = R(g[0], c(*g[1:]))
        for i in range(n):
            gg = g[:i] + (mul(g[i], g[i + 1]),) + g[i + 2:]
            tot = vadd(tot, vscale((-1) ** (i + 1), c(*gg)))
        tot = vadd(tot, vscale((-1) ** (n + 1), c(*g[:n])))
        return tot
    return dc


def T(c, n):
    """(T c)(g_1..g_n) = sum_delta R(r_{g_1...g_n delta}) c(h(g_1,delta_1),...,h(g_n,delta_n)),
    delta_i = g_{i+1}...g_n delta."""
    def Tc(*g):
        assert len(g) == n
        tot = ZERO
        for d in Delta:
            deltas = []
            cur = d
            for i in range(n - 1, -1, -1):
                deltas.append(cur)
                cur = coset(g[i], cur)
            deltas = deltas[::-1]  # deltas[i] = g_{i+1}...g_n d
            full = cur  # g_1...g_n d
            args = tuple(h(g[i], deltas[i]) for i in range(n))
            # R(r_full) applied to c(...)
            val = c(*args)
            tot = vadd(tot, R(r[full], val))
        return tot
    return Tc


results = []


def check(name, ok):
    results.append(ok)
    print(("PASS " if ok else "FAIL ") + name)


# cocycle identity of h
ok = True
for _ in range(2000):
    g, k = random.choice(G), random.choice(G)
    d = random.choice(Delta)
    if h(mul(g, k), d) != mul(h(g, coset(k, d)), h(k, d)):
        ok = False
check("h(gk,delta) = h(g,k delta) h(k,delta)", ok)

for n in (0, 1, 2):
    ok = True
    for trial in range(3):
        c = cochain("c%d_%d" % (n, trial))
        lhs = d_tgt(T(c, n), n)
        rhs = T(d_src(c, n), n + 1)
        for _ in range(400):
            g = tuple(random.choice(G) for _ in range(n + 1))
            if lhs(*g) != rhs(*g):
                ok = False
    check("d T = T d on random degree-%d cochains (target action theta*rho)" % n, ok)

# a genuine 1-cocycle on N: crossed homomorphism from a coboundary plus N-invariant hom part
# (coboundary of random m) -> its transfer is a G-cocycle and equals coboundary of T(m)
m = (3, 5)
b = lambda x: vadd(act(x, m), vscale(-1, m))
Tb = T(b, 1)
ok = True
for _ in range(500):
    g, k = random.choice(G), random.choice(G)
    if Tb(mul(g, k)) != vadd(Tb(g), R(g, Tb(k))):
        ok = False
check("T(coboundary) satisfies the cocycle identity with target action theta*rho", ok)
TQ = sum_ = ZERO
for d in Delta:
    sum_ = vadd(sum_, R(r[d], m))
ok = all(Tb(g) == vadd(R(g, sum_), vscale(-1, sum_)) for g in random.sample(G, 300))
check("degree 0: T(dQ) = d(sum_delta theta(r_delta) rho(r_delta) Q)", ok)

print("\n%d/%d PASS" % (sum(results), len(results)))
