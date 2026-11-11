"""E3: genus of the trivial-witness curve m(m - B(q)) = h² on an honest line of the test-site toy.
Tests in K0 = Q(√2) as c + d√2 (small random), Θ = Tr W^{-1} = (W + W')/(W W'), σ = a/Θ, B = R0 σ².
Odd-order points of m(m - B(q)) on P¹_q = branch points; genus = #branch/2 - 1."""
import random
from sympy import symbols, sqrt, expand, Poly, gcd, factor_list, together, fraction, Rational, degree
random.seed(2)
q = symbols('q')
r2 = sqrt(2)
def run(R0, tests, m):
    a = 1 - R0*q**2; R = R0*a**2
    W = 1; Wc = 1
    for (c, d) in tests:
        W = expand(W*(1 + R*(c + d*r2)**2)); Wc = expand(Wc*(1 + R*(c - d*r2)**2))
    num_T = expand(W + Wc); den_T = expand(W*Wc)        # Θ = num_T/den_T (rational in q)
    # m(m - B) = m(m Θ² - R0 a²)/Θ²  ->  odd part = m Θnum²... use  m(m num_T² - R0 a² den_T²) / num_T²
    F = Poly(expand(m*num_T**2 - R0*a**2*den_T**2), q)
    F = Poly(F.as_expr().expand(), q, domain='QQ')
    g = gcd(F, F.diff(q))
    sqfree_deg = F.degree() - 2*g.degree() if g.degree() > 0 else F.degree()
    nbranch = sum(e % 2 for _, e in [(f, e) for f, e in factor_list(F.as_expr())[1] for _ in range(f.as_poly(q).degree() if False else 1)])
    # count odd-multiplicity roots (with degree) and the point at infinity
    odd = 0
    for f, e in factor_list(F.as_expr())[1]:
        if e % 2: odd += Poly(f, q).degree()
    inf_odd = F.degree() % 2              # deg F odd -> branch at infinity
    nb = odd + inf_odd
    return F.degree(), nb, nb//2 - 1
for trial in range(3):
    R0 = Rational(random.choice([3, 5, 7, 11]) * 331)
    tests = [(random.randint(-3, 3), random.randint(-2, 2)) for _ in range(6)]
    for m in (1, 2):
        dF, nb, g = run(R0, tests, m)
        print("trial", trial, "m", m, "deg", dF, "branch points", nb, "genus", g)
