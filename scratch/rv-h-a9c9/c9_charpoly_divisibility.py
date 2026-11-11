"""C9: an Euler-factor (total characteristic polynomial) identity alone does not imply that a
given representation is a constituent.  Abstract counterexample: G = Z/2 x Z/2, V = 1+a+b,
U = ab.  For every g, charpoly_U(g) divides charpoly_V(g), but U is not a constituent of V.
(Hence the K_f-linear trace statement, or the existence of all rho_{f^sigma} plus Brauer-Nesbitt,
is needed to pass from Shimura's zeta identity to 'r_5 is a constituent of V_5(A_f)'.)"""
import sympy as sp
X = sp.symbols('X')
G = [(0, 0), (1, 0), (0, 1), (1, 1)]
chi = {'1': lambda g: 1, 'a': lambda g: (-1)**g[0], 'b': lambda g: (-1)**g[1],
       'ab': lambda g: (-1)**(g[0] + g[1])}
V = ['1', 'a', 'b']; U = 'ab'
ok = True
for g in G:
    PV = sp.prod([X - chi[c](g) for c in V]); PU = X - chi[U](g)
    r = sp.rem(PV, PU, X)
    print(g, "charpoly_V =", sp.factor(PV), " charpoly_U =", PU, " divides:", r == 0)
    ok &= (r == 0)
inner = sum(chi[U](g) * sum(chi[c](g) for c in V) for g in G) / len(G)
print("divisibility at every g:", ok, "; multiplicity <U,V> =", inner)
