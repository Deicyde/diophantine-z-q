from fractions import Fraction as Fr
from math import gcd
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form
def run(n):
    def mul(u,v): return (u[0]*v[0]-n*u[1]*v[1], u[0]*v[1]+u[1]*v[0])
    def inv(u):
        N = u[0]**2 + n*u[1]**2
        return (u[0]/N, -u[1]/N)
    def span(gens):
        den = 1
        for g in gens:
            for c in g: den = den*c.denominator//gcd(den,c.denominator)
        M = Matrix([[int(g[0]*den), int(g[1]*den)] for g in gens])
        H = hermite_normal_form(M.T).T
        return sorted([ (Fr(int(H[i,0]),den), Fr(int(H[i,1]),den)) for i in range(H.rows) if any(H[i,j]!=0 for j in range(2))])
    b = [(Fr(6),Fr(4)), (Fr(3-4*n),Fr(8))]
    t = (Fr(1,4*(n+1)), Fr(1,4*(n+1)))
    tp = (Fr(2*n+15,4*(n+9)), Fr(1,4*(n+9)))
    L, LN = [(Fr(1),Fr(0)), t], [(Fr(1,32),Fr(0)), t]
    Lp, LNp = [(Fr(1),Fr(0)), tp], [(Fr(1,32),Fr(0)), tp]
    X = span([mul(x,y) for x in b for y in Lp]); XN = span([mul(x,y) for x in b for y in LNp])
    # find c with X = c L: try c = each candidate: c = X-element s.t. c^{-1} X = L
    for c0 in X + [ (X[0][0]+X[1][0], X[0][1]+X[1][1]) ]:
        ci = inv(c0)
        if span([mul(ci,x) for x in X]) == span(L) and span([mul(ci,x) for x in XN]) == span(LN):
            return c0
    return None, X, XN
for n in [5,13,21,29,37,45,53,61,69,77,85,93,101,109,165,205,221,1005]:
    print(n, run(n))
