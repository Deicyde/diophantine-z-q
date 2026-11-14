"""period-glue: linear_combination coefficients for Nf(t0)_ij = Omega0_ij * dF(t0), t0 = sqrt2 + i.
Variables s = sqrt2, I = i; reduce modulo s^2 - 2, I^2 + 1 (Groebner division).
Run: ~/pyenv/bin/python -I omega0_lc.py"""
import sympy as sp
s, I = sp.symbols('s I')
t = s + I
Nf = [[s*(t**2/2 + t - sp.Rational(3,2)) - t**2/2 - sp.Rational(3,2), s*(-t**2/2 - t + sp.Rational(3,2)) + t**2 + 3],
      [s*(-t**2/2 - t + sp.Rational(3,2)) + t**2 + 3, s*(t**2 + 2*t - 3) - t**2 - 3]]
dF = -s*(t-3)*(t+1)/2
Om0 = [[(-1+I)/2, 1], [1, -1+I]]
G = [s**2 - 2, I**2 + 1]
for i in range(2):
    for j in range(2):
        e = sp.expand(Nf[i][j] - Om0[i][j]*dF)
        q, r = sp.reduced(e, G, s, I)
        print(i, j, "remainder", r, "| coeff(s^2-2):", sp.factor(q[0]), "| coeff(I^2+1):", sp.factor(q[1]))
print("dF(t0) reduced:", sp.reduced(sp.expand(dF), G, s, I)[1])
