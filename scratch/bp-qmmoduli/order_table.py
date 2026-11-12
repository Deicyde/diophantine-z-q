# Structure constants of O = Z<1, i, (1+j)/2, (i+k)/2> in B = (2,-3)/Q, k = ij.
# Quaternion product with i^2 = a=2, j^2 = b=-3, k = ij, k^2 = -ab = 6.
import sympy as sp
a, b = 2, -3
def mul(x, y):
    x0,x1,x2,x3 = x; y0,y1,y2,y3 = y
    return (x0*y0 + a*x1*y1 + b*x2*y2 - a*b*x3*y3,
            x0*y1 + x1*y0 - b*x2*y3 + b*x3*y2,
            x0*y2 + x2*y0 + a*x1*y3 - a*x3*y1,
            x0*y3 + x3*y0 + x1*y2 - x2*y1)
R = sp.Rational
E = [(1,0,0,0),(0,1,0,0),(R(1,2),0,R(1,2),0),(0,R(1,2),0,R(1,2))]
M = sp.Matrix([list(e) for e in E]).T  # columns = basis
def coords(v): return list(M.solve(sp.Matrix(v)))
n = sp.symbols('n0:4'); m = sp.symbols('m0:4')
x = [sum(n[k]*E[k][c] for k in range(4)) for c in range(4)]
y = [sum(m[k]*E[k][c] for k in range(4)) for c in range(4)]
p = [sp.expand(t) for t in mul(x,y)]
cs = [sp.expand(c) for c in coords(p)]
for k,c in enumerate(cs):
    print(f"m{k} =", c)
    assert all(t.is_integer for t in sp.Poly(c, *n, *m).coeffs())
# conj and dagger x -> mu^{-1} conj(x) mu, mu = 2j + k
conj = lambda v: (v[0], -v[1], -v[2], -v[3])
mu = (0,0,2,1); muinv = (0,0,R(-1,3),R(-1,6))
print("mu*muinv", mul(mu,muinv))
for e in E:
    d = mul(mul(muinv, conj(e)), mu)
    print("dagger", e, "->", d, coords(d))
    print("conj  ", e, "->", coords(conj(e)))
# Atkin-Lehner elements and normalizing
def nrd(v): return v[0]**2 - a*v[1]**2 - b*v[2]**2 + a*b*v[3]**2
for w in [(1,1,1,0),(0,0,1,0),mu]:
    wi = tuple(sp.Rational(c)/nrd(w) for c in conj(w))
    print("w",w,"nrd",nrd(w))
    for e in E:
        print("   ", coords(mul(mul(w,e),wi)), coords(mul(mul(wi,e),w)))
print("---- dag x * x, positivity, AL relations")
X = sp.symbols('x0:4')
d = mul(mul(muinv, conj(X)), mu)
dx = [sp.expand(t) for t in mul(d, X)]
print("dag x * x =", dx)
tr = sp.expand(2*mul(X, d)[0])
print("trd(x dag x) =", tr, sp.Matrix(4,4,lambda i,j: sp.diff(tr,X[i],X[j])/2).is_positive_definite)
for v in [(1,1,0,0),(0,0,1,0),(0,0,0,1),(0,0,1,1),(1,0,1,0)]:
    print(v, [ (t.subs(dict(zip(X,v)))) for t in dx])
w2=(1,1,1,0); w3=(0,0,1,0)
p = mul(mul(w2,w3), muinv); print("w2 w3 mu^-1 =", p, coords(p), nrd(p))
print("w2^2 =", mul(w2,w2), "w2 w3 w2^-1 w3^-1 :", mul(mul(w2,w3), mul(tuple(R(c,2) for c in conj(w2)), tuple(R(c,3) for c in conj(w3)))))
