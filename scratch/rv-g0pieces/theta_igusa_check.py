"""Numerical check of the theta normalization behind ThetaPointOfFibre's constant 3779136.
Claim checked: for a genus-2 curve y^2 = f(x) (sextic, real roots) with Igusa-Clebsch
invariants I4, I10 and a period matrix Omega of its Jacobian,
    I4^5 / I10^2 = (sum_{10 even m} theta_m(Omega)^8)^5 / (prod_{even m} theta_m(Omega)^2)^2.
Both sides are invariant under weighted rescaling / Sp4(Z), so no theta labelling or
symplectic-basis convention enters (only: Omega symmetric with Im Omega > 0).
Then with Igusa's J's (J2 = I2/8, J4 = (4 J2^2 - I4)/96, J10 = I10/4096) one gets
J2^2 - 24 J4 = I4/4 and -J10/4 = -I10/2^14, i.e. psi4 = 2^-2 sum theta^8 and
chi10 = -2^-14 prod theta^2 in Lin-Yang's identification (psi4 = J2^2-24J4, chi10 = -J10/4),
which with Lin-Yang's Igusa vector [12(j+1), 6(j^2+j+1), ., j^3] gives
3779136 (prod theta)^4/(sum theta^8)^5 = j."""
import itertools
import mpmath as mp
mp.mp.dps = 40

def ic_invariants(e):
    pairs = lambda S: [(a, b) for a, b in itertools.combinations(S, 2)]
    d = lambda i, j: (e[i] - e[j]) ** 2
    idx = range(6)
    I4 = mp.mpf(0)
    seen = set()
    for T in itertools.combinations(idx, 3):
        U = tuple(i for i in idx if i not in T)
        key = frozenset([T, U])
        if key in seen: continue
        seen.add(key)
        t = mp.mpf(1)
        for (a, b) in pairs(T) + pairs(U): t *= d(a, b)
        I4 += t
    assert len(seen) == 10
    I10 = mp.mpf(1)
    for (a, b) in pairs(idx): I10 *= d(a, b)
    return I4, I10

def periods(e):
    f = lambda x: mp.fprod([x - r for r in e])
    w = []
    for k in range(5):
        a, b = e[k], e[k + 1]
        g0 = lambda x: 1 / mp.sqrt(abs(f(x)))
        g1 = lambda x: x / mp.sqrt(abs(f(x)))
        w.append(mp.matrix([mp.quad(g0, [a, b]), mp.quad(g1, [a, b])]))
    # f<0 on intervals 0,2,4 (imaginary periods), f>0 on 1,3 (real periods)
    v = [2 * w[k] * (1j if k % 2 == 0 else 1) for k in range(5)]
    return v

def theta_consts(Om, N=12):
    res = {}
    for a in itertools.product((0, 1), repeat=2):
        for b in itertools.product((0, 1), repeat=2):
            if (a[0] * b[0] + a[1] * b[1]) % 2: continue
            s = mp.mpc(0)
            for n1 in range(-N, N + 1):
                for n2 in range(-N, N + 1):
                    x = (n1 + a[0] / 2, n2 + a[1] / 2)
                    q = sum(x[i] * Om[i, j] * x[j] for i in range(2) for j in range(2))
                    l = x[0] * b[0] / 2 + x[1] * b[1] / 2
                    s += mp.exp(mp.pi * 1j * q + 2 * mp.pi * 1j * l)
            res[(a, b)] = s
    assert len(res) == 10
    return res

def check(e):
    e = [mp.mpf(x) for x in e]
    v = periods(e)
    # relation among the cut cycles: v0 +- v2 +- v4 = 0
    rel = min((mp.norm(v[0] + s2 * v[2] + s4 * v[4]), s2, s4) for s2 in (1, -1) for s4 in (1, -1))
    print("cut-cycle relation residual:", mp.nstr(rel[0], 5))
    A = mp.matrix(2, 2); A[:, 0] = v[0]; A[:, 1] = v[2]
    best = None
    cands = {}
    for c in itertools.product((-1, 0, 1), repeat=4):
        cands[c] = c[0] * v[1] + c[1] * v[3] + c[2] * v[0] + c[3] * v[2]
    for c1, c2 in itertools.product(cands, repeat=2):
        B = mp.matrix(2, 2); B[:, 0] = cands[c1]; B[:, 1] = cands[c2]
        if abs(B[0,0]*B[1,1]-B[0,1]*B[1,0]) < 1e-20: continue
        Om = mp.inverse(A) * B
        sym = abs(Om[0, 1] - Om[1, 0])
        Im = mp.matrix([[mp.im(Om[i, j]) for j in range(2)] for i in range(2)])
        if sym < 1e-15 and Im[0, 0] > 0 and Im[0,0]*Im[1,1]-Im[0,1]*Im[1,0] > 0:
            score = min(Im[0, 0], Im[1, 1])
            if best is None or score > best[0]: best = (score, Om, (c1, c2))
    assert best is not None, "no symmetric period matrix found"
    Om = best[1]
    # reduce a little: the theta sums converge for any Om in H2; N=12 is ample if min Im > 0.3
    print("Omega =", [[mp.nstr(Om[i, j], 8) for j in range(2)] for i in range(2)], "B-combo", best[2])
    th = theta_consts(Om)
    h4 = sum(t ** 8 for t in th.values())
    h10 = mp.fprod([t ** 2 for t in th.values()])
    I4, I10 = ic_invariants(e)
    lhs = I4 ** 5 / I10 ** 2
    rhs = h4 ** 5 / h10 ** 2
    print("I4^5/I10^2            =", mp.nstr(lhs, 25))
    print("h4^5/h10^2 (thetas)   =", mp.nstr(rhs, 25))
    print("relative difference   =", mp.nstr(abs(lhs - rhs) / abs(lhs), 5))
    return abs(lhs - rhs) / abs(lhs)

if __name__ == "__main__":
    r1 = check([-2, -1, 0.5, 1.3, 2.7, 4])
    r2 = check([-3, -0.7, 0.2, 1.1, 1.9, 5.5])
    assert r1 < 1e-15 and r2 < 1e-15
    print("CHECK PASSED")
