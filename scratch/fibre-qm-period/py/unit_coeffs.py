"""fibre-qm-period: coefficients for the Lean proof of qmOrbit_unit (orbit of (tau,1) under iota(O)
equals the orbit of iota(1+i)(tau,1)). Checks the 8 vector identities and prints, per component, the
quotient q with LHS - RHS = q * (r^2 - 2), r = sqrt 2 (for `linear_combination q * s`).
Run: ~/pyenv/bin/python -I unit_coeffs.py"""
import sympy as sp
r, t = sp.symbols('r t')
def gens(a, b):
    return [(a, b), (r*a, -(r*b)), ((a-3*b)/2, (a+b)/2), (r*(a-3*b)/2, -(r*(a+b))/2)]
g = gens(t, 1)
h = gens((1+r)*t, 1-r)
fwd = {0: {0: -1, 1: 1}, 1: {0: 2, 1: -1}, 2: {1: 1, 2: -1, 3: -1}, 3: {0: 2, 2: -2, 3: -1}}   # g_k = sum c_j h_j
rev = {0: {0: 1, 1: 1}, 1: {0: 2, 1: 1}, 2: {1: 1, 2: 1, 3: -1}, 3: {0: 2, 2: -2, 3: 1}}      # h_k = sum c_j g_j
for name, (L, R, table) in {"fwd": (g, h, fwd), "rev": (h, g, rev)}.items():
    for k, comb in table.items():
        out = []
        for i in range(2):
            diff = sp.expand(L[k][i] - sum(c*R[j][i] for j, c in comb.items()))
            q, rem = sp.div(diff, r**2 - 2, r)
            assert sp.simplify(rem) == 0, (name, k, i, rem)
            out.append(sp.factor(q))
        print(name, k, comb, "coeffs:", out)
