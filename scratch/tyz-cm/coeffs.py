import sympy as sp
n = sp.symbols('n')
# elements of K as (re, im) in basis 1, w ; w^2 = -n
def mul(a,b): return (sp.expand(a[0]*b[0]-n*a[1]*b[1]), sp.expand(a[0]*b[1]+a[1]*b[0]))
c = (sp.Rational(1)*(5*n+9)/(n+9), -2*(n+3)/(n+9))
tau = (1/(4*(n+1)), 1/(4*(n+1)))
taup = ((2*n+15)/(4*(n+9)), 1/(4*(n+9)))
b = [(6,4), (3-4*n, 8)]
for N, name in [(1, "lat"), (32, "latN")]:
    one = (sp.Rational(1, N), 0)
    base = [mul(c, one), mul(c, tau)]   # c*L
    gens = [mul(bi, l) for bi in b for l in [one, taup]]
    x, y = sp.symbols('x y')
    print("==", name, ": products in basis (c/N, c tau)")
    for g in gens:
        sol = sp.solve([sp.together(x*base[0][0]+y*base[1][0]-g[0]), sp.together(x*base[0][1]+y*base[1][1]-g[1])],[x,y])
        print("  ", sp.factor(sol[x]), " | ", sp.factor(sol[y]))
    # inverse: c/N and c tau in terms of gens: solve using 2 of them? use all 4 -> find integer combination
    M = sp.Matrix([[sp.factor(sp.solve([sp.together(x*base[0][0]+y*base[1][0]-g[0]), sp.together(x*base[0][1]+y*base[1][1]-g[1])],[x,y])[v]) for v in (x,y)] for g in gens])
    print("  matrix rows = gens in basis; det of 2x2 minors:")
    for i in range(4):
        for j in range(i+1,4):
            print("   ", i, j, sp.factor(M[i,0]*M[j,1]-M[i,1]*M[j,0]))
