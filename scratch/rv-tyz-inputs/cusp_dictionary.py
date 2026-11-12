"""Check TYZ fact (3) (L1393-1404, cited from Tian 2014): the identification X_0(32) -> A sends the cusps to
A[(1+i)^3] = tau(1/2 Z[i] / (1+i) Z[i]) as
  [oo]->0, [0]->1/2, [1/2]->-1/2, [1/16]->1, [+-1/4]->+-i/2, [+-1/8]->(1+-i)/2,
where tau : C/(1+i)Z[i] -> A(C) maps R/2Z onto A(R) (tau fixed up to sign).

A : 2y^2 = x^3 + x is isomorphic over Q to E = 32a1 : Y^2 = X^3 + 4X (X = 2x, Y = 4y), the optimal curve, i.e.
X_0(32) itself (modular degree 1, Manin constant 1). The modular parametrisation is
phi(z) = 2 pi i int_{i oo}^{z} f(w) dw  mod Lambda_E, and by PARI's normalisation (msfromell)
phi(a/c) = x^+([oo, a/c]) Omega^+ + x^-([oo, a/c]) i Omega^-.
For E: Lambda_E = c (1+i) Z[i] with c = Omega^+/2 (checked below), so the tau-coordinate is
phi(a/c)/c = 2 x^+ + 2 i x^-  (mod (1+i)Z[i]).
"""
import cypari2
pari = cypari2.Pari()
E = pari.ellinit([0, 0, 0, 4, 0])
om = pari('(e)->e.omega')(E)
Op = om[0]
c = Op / 2
# lattice check: omega = [2c, c(1-i)]
print('omega =', om, ' c =', c, ' lattice = c(1+i)Z[i]:',
      abs(om[0] - 2 * c) < 1e-12 and abs(om[1] - c * (1 - pari('I'))) < 1e-12)
cinf = 1  # one real component (disc < 0)
Om_minus = -2 / cinf * pari.imag(om[1])
print('Omega^- =', Om_minus, ' (= 2c:', abs(Om_minus - 2 * c) < 1e-12, ')')
res = pari.msfromell(E, 0)
M, xs = res[0], res[1]
xp, xm = xs[0], xs[1]
oo = pari('oo')


def red(z):
    """reduce Gaussian rational z modulo (1+i)Z[i] to a canonical representative in {0,1/2,-1/2,1,i/2,-i/2,(1+i)/2,(1-i)/2}."""
    reps = {'0': 0, '1/2': pari('1/2'), '-1/2': pari('-1/2'), '1': 1, 'i/2': pari('I/2'), '-i/2': pari('-I/2'),
            '(1+i)/2': pari('(1+I)/2'), '(1-i)/2': pari('(1-I)/2')}
    for name, r in reps.items():
        d = (z - r) / pari('1+I')
        if pari.denominator(pari.real(d)) == 1 and pari.denominator(pari.imag(d)) == 1:
            return name
    return None


claimed = {'oo': '0', '0': '1/2', '1/2': '-1/2', '1/16': '1', '1/4': 'i/2', '-1/4': '-i/2',
           '1/8': '(1+i)/2', '-1/8': '(1-i)/2'}
neg = {'0': '0', '1/2': '-1/2', '-1/2': '1/2', '1': '1', 'i/2': '-i/2', '-i/2': 'i/2',
       '(1+i)/2': '(1-i)/2', '(1-i)/2': '(1+i)/2'}
computed = {}
for cs in claimed:
    if cs == 'oo':
        computed[cs] = '0'
        continue
    cusp = pari(cs)
    a = pari.mseval(M, xp, [oo, cusp])
    b = pari.mseval(M, xm, [oo, cusp])
    zt = 2 * a + 2 * b * pari('I')
    computed[cs] = red(zt)
    # numerical cross-check: the point on E is torsion of order | 4 and lies in E(Q(i))
    P = pari.ellztopoint(E, a * Op + b * pari('I') * Om_minus)
    print(f'cusp {cs:>5}: x+ = {a}, x- = {b}, tau-coordinate = {zt} -> {computed[cs]:>8}   claimed {claimed[cs]:>8}   '
          f'point on E ~ {[pari.round(pari.real(t) * 10**6) / 10**6 + pari.round(pari.imag(t) * 10**6) / 10**6 * pari("I") for t in P] if len(P) == 2 else P}')
ok_plus = all(computed[k] == claimed[k] for k in claimed)
ok_minus = all(computed[k] == neg[claimed[k]] for k in claimed)
print('matches table with tau:', ok_plus, '; with -tau:', ok_minus)
print('bijective onto A[(1+i)^3]:', len(set(computed.values())) == 8)
print('RESULT', 'OK' if (ok_plus or ok_minus) else 'MISMATCH')
