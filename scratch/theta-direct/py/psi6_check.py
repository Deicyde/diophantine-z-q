"""theta-direct: check that Igusa's theta expression psi6T (theta-glue, ThetaDirect/Glue.lean) is invariant, as a
polynomial in the four second-order theta constants u_c (t_m = Sq m u), under the signed permutations of gt-theta's
squared transformation laws at M4 and M6 (ThetaModularityM46.lean sq4/sq6):
  t_m(M.Omega) = -D * exp(pi i N_M(m)/4) * t_{sigma_M(m)}(Omega),
so (t_a t_b t_c)^2 picks up D^6 * prod e^2, e^2 = (-1)^(N/2).  Exact (sympy)."""
import re, itertools, sympy as sp
src = open('ZInQKernel/Contrib/OneProof/ThetaDirect/Glue.lean').read()
blk = src[src.index('def psi6T (t : PkgI1.Char2 → ℂ) : ℂ :='):]
blk = blk[:blk.index('\n\n')]
terms = re.findall(r'([+-])?\s*\(t \(!\[(\d), (\d)\], !\[(\d), (\d)\]\) \* t \(!\[(\d), (\d)\], !\[(\d), (\d)\]\) \* t \(!\[(\d), (\d)\], !\[(\d), (\d)\]\)\) \^ 2', blk)
print('psi6T terms', len(terms))
T = []
for g in terms:
    sgn = -1 if g[0] == '-' else 1
    v = list(map(int, g[1:]))
    chars = [((v[0], v[1]), (v[2], v[3])), ((v[4], v[5]), (v[6], v[7])), ((v[8], v[9]), (v[10], v[11]))]
    T.append((sgn, chars))
u = {c: sp.Symbol(f'u{c[0]}{c[1]}') for c in itertools.product((0, 1), repeat=2)}
def Sq(m):
    a, b = m
    tot = 0
    for c in itertools.product((0, 1), repeat=2):
        ca = ((c[0] + a[0]) % 2, (c[1] + a[1]) % 2)
        tot += (-1) ** (ca[0] * b[0] + ca[1] * b[1]) * u[c] * u[ca]
    return sp.expand(tot)
def psi6(tf):
    return sp.Rational(1, 4) * sum(s * (tf(c[0]) * tf(c[1]) * tf(c[2])) ** 2 for s, c in T)
f2 = lambda x: x % 2
def sigma6(m):
    (a0, a1), (b0, b1) = m
    return ((f2(-b1), f2(b0)), (f2(a1 - b1 + 1 - b0), f2(-a0 + 2 * b0 + 2 + b1)))
def N6(m):
    (a0, a1), (b0, b1) = m
    return 4*a0*b0 + 4*a1*b1 - 2*b1**2 + 4*b1 - 4*b0**2 - 8*b0 - 4*b0*b1
def sigma4(m):
    (a0, a1), (b0, b1) = m
    return ((f2(a0 + b1), f2(a1 + b0)), (f2(a0 - 2*a1 + b1 - b0 + 1), f2(-2*a0 + 2*a1 + 2*b0 - b1 + 2)))
def N4(m):
    (a0, a1), (b0, b1) = m
    return (4*a0*a1 + 4*a1*b1 + 4*a0*b0 - 2*(a0 + b1)**2 - 4*(a0 + b1) - 4*(a1 + b0)**2 - 8*(a1 + b0)
            + 4*(a0 + b1)*(a1 + b0))
even = [m for m in itertools.product(itertools.product((0, 1), repeat=2), repeat=2)
        if (m[0][0]*m[1][0] + m[0][1]*m[1][1]) % 2 == 0]
base = sp.expand(psi6(Sq))
for name, sig, N in [('M6', sigma6, N6), ('M4', sigma4, N4)]:
    assert all(N(m) % 2 == 0 for m in even)
    # e_m^2 = exp(pi i N/2) = (-1)^(N/2)  (N even);  t'_m = -D e_m t_{sigma m}; psi6 has only squares of products
    tr = sp.expand(sp.Rational(1, 4) * sum(s * (-1) ** ((N(c[0]) + N(c[1]) + N(c[2])) // 2)
                                          * (Sq(sig(c[0])) * Sq(sig(c[1])) * Sq(sig(c[2]))) ** 2 for s, c in T))
    print(name, 'psi6 invariant (formal in u):', sp.expand(tr - base) == 0)
    print(name, 'sigma on even chars:', {m: sig(m) for m in even})
    print(name, 'N:', {m: N(m) for m in even})

# is the invariance already formal in the ten t_m (no Riemann relations)?
tt = {m: sp.Symbol('t_%d%d%d%d' % (m[0][0], m[0][1], m[1][0], m[1][1])) for m in even}
base_t = sp.expand(sp.Rational(1, 4) * sum(s * (tt[c[0]] * tt[c[1]] * tt[c[2]]) ** 2 for s, c in T))
for name, sig, N in [('M6', sigma6, N6), ('M4', sigma4, N4)]:
    tr = sp.expand(sp.Rational(1, 4) * sum(s * (-1) ** ((N(c[0]) + N(c[1]) + N(c[2])) // 2)
                                          * (tt[sig(c[0])] * tt[sig(c[1])] * tt[sig(c[2])]) ** 2 for s, c in T))
    print(name, 'psi6 invariant formally in t:', sp.expand(tr - base_t) == 0)

blk12 = src[src.index('def chi12T (t : PkgI1.Char2 → ℂ) : ℂ :='):]
blk12 = blk12[:blk12.index('\n\n')]
pat = r'\(' + r' \* '.join([r't \(!\[(\d), (\d)\], !\[(\d), (\d)\]\)'] * 6) + r'\) \^ 2'
terms12 = re.findall(pat, blk12)
print('chi12T terms', len(terms12))
T12 = []
for g in terms12:
    v = list(map(int, g))
    T12.append([((v[4*i], v[4*i+1]), (v[4*i+2], v[4*i+3])) for i in range(6)])
base12 = sp.expand(sum(sp.Mul(*[tt[c] for c in cs]) ** 2 for cs in T12))
for name, sig, N in [('M6', sigma6, N6), ('M4', sigma4, N4)]:
    tr = sp.expand(sum((-1) ** (sum(N(c) for c in cs) // 2) * sp.Mul(*[tt[sig(c)] for c in cs]) ** 2 for cs in T12))
    print(name, 'chi12 invariant formally in t:', sp.expand(tr - base12) == 0)
