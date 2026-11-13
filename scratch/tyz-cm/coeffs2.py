import sympy as sp
k = sp.symbols('k'); n = 8*k+5
def mul(a,b): return (sp.expand(a[0]*b[0]-n*a[1]*b[1]), sp.expand(a[0]*b[1]+a[1]*b[0]))
c = ((5*n+9)/(n+9), -2*(n+3)/(n+9))
tau = (1/(4*(n+1)), 1/(4*(n+1)))
taup = ((2*n+15)/(4*(n+9)), 1/(4*(n+9)))
b = [(6,4), (3-4*n, 8)]
x, y = sp.symbols('x y')
for N, name in [(1, "lat"), (32, "latN")]:
    one = (sp.Rational(1, N), 0)
    base = [mul(c, one), mul(c, tau)]
    gens = [mul(bi, l) for bi in b for l in [one, taup]]
    M = []
    for g in gens:
        sol = sp.solve([sp.together(x*base[0][0]+y*base[1][0]-g[0]), sp.together(x*base[0][1]+y*base[1][1]-g[1])],[x,y])
        M.append([sp.expand(sp.simplify(sol[x])), sp.expand(sp.simplify(sol[y]))])
    print("==", name, "gens = M * (c/N, c tau):", M)
    M = sp.Matrix(M)
    # e1 = (1,0), e2 = (0,1) as integer combos of rows: use rows 0,1 (det d01) and 2,3 (det d23)
    A01 = M[0:2,:]; A23 = M[2:4,:]
    d01 = sp.factor(A01.det()); d23 = sp.factor(A23.det())
    print(" d01", d01, "d23", d23)
    # Bezout: u*d01 + v*d23 = 1 with polynomials in k
    for e in [sp.Matrix([[1,0]]), sp.Matrix([[0,1]])]:
        # e*d01 = l01 * A01 -> l01 = e*adj(A01) ; e*d23 = l23*A23
        l01 = sp.expand(e*A01.adjugate()); l23 = sp.expand(e*A23.adjugate())
        print("  e", list(e), " l01", list(l01), " l23", list(l23))
