"""t28-igusa: linear_combination coefficients for the SO(3) lemma (z = mu * z')."""
import sympy as sp
a,b,c,d,z0,z1,z2 = sp.symbols('a b c d z0 z1 z2')
E1 = c**2*z0 - c*d*z1 + d**2*z2
E2 = a**2*z0 - a*b*z1 + b**2*z2
H = (a*d-b*c)**2 - 1
mu = -(2*z0*a*c + 2*z2*b*d - z1*(a*d+b*c))
zp = [b*d, a*d+b*c, a*c]
z = [z0, z1, z2]
# z_k - mu*zp_k = alpha*E1 + beta*E2 + gamma*H, with gamma = -z_k (since z_k*(det^2) ...)
for k in range(3):
    g = sp.expand(z[k] - mu*zp[k] + z[k]*H)   # = z_k*det^2 - mu*zp_k, should be in ideal(E1,E2)
    G = sp.groebner([E1, E2], z0, z1, z2, a, b, c, d, order='lex')
    q, r = sp.reduced(g, [E1, E2], z0, z1, z2, a, b, c, d)
    print(k, "remainder", sp.expand(r), "coeffs", [sp.factor(t) for t in q])
