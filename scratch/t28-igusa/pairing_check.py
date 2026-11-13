"""t28-igusa: check the invariant pairings used in Mestre.lean (exact, symbolic).
p6(f|M, g|M) = det^6 p6(f,g), pair(q|M, p|M) = det^2 pair(q,p), cub(q1|M,q2|M,q3|M) = cub(q1,q2,q3)|M."""
import sympy as sp
a,b,c,d,x = sp.symbols('a b c d x')
f = sp.symbols('f0:7'); g = sp.symbols('g0:7')
def act(v, n):
    P = sp.expand(sum(v[k]*(a*x+b)**k*(c*x+d)**(n-k) for k in range(n+1)))
    return [P.coeff(x, i) for i in range(n+1)]
w = [60, -10, 4, -3, 4, -10, 60]
p6 = lambda u, v: sum(w[i]*u[i]*v[6-i] for i in range(7))
det = a*d - b*c
print("p6 invariant:", sp.expand(p6(act(f,6), act(g,6)) - det**6*p6(f, g)) == 0)
q = sp.symbols('q0:3'); p = sp.symbols('p0:3'); r = sp.symbols('r0:3')
pair = lambda u, v: 2*u[0]*v[2] + 2*u[2]*v[0] - u[1]*v[1]
print("pair invariant:", sp.expand(pair(act(q,2), act(p,2)) - det**2*pair(q,p)) == 0)
def cub(u, v, t):
    P = sp.expand(sum(u[i]*x**i for i in range(3))*sum(v[i]*x**i for i in range(3))*sum(t[i]*x**i for i in range(3)))
    return [P.coeff(x, i) for i in range(7)]
print("cub equivariant:", all(sp.expand(l - r_) == 0 for l, r_ in zip(cub(act(q,2), act(p,2), act(r,2)), act(cub(q,p,r), 6))))
