import sympy as sp
a=sp.symbols('a0:4'); b=sp.symbols('b0:4')
def mul(n,m):
    return [m[0]*n[0]+2*m[1]*n[1]+2*m[1]*n[3]-m[2]*n[2]+2*m[3]*n[3],
            m[0]*n[1]+m[1]*n[0]+m[1]*n[2]-m[2]*n[3]+m[3]*n[2],
            m[0]*n[2]-2*m[1]*n[3]+m[2]*n[0]+m[2]*n[2]+2*m[3]*n[1],
            m[0]*n[3]-m[1]*n[2]+m[2]*n[1]+m[2]*n[3]+m[3]*n[0]]
def conj(n): return [n[0]+n[2],-n[1],-n[2],-n[3]]
def nrd(n): return n[0]**2+n[0]*n[2]+n[2]**2-2*(n[1]**2+n[1]*n[3]+n[3]**2)
# check nrd: conj(n)*n
print([sp.expand(x) for x in mul(conj(list(a)),list(a))], sp.expand(nrd(a)))
gens = [sp.expand(x) for x in mul(conj(list(a)),list(b))] + [sp.expand(x) for x in mul(list(a),conj(list(b)))] + [nrd(a), nrd(b)]
gens=[g for g in gens if g!=0]
G = sp.groebner(gens, *a, *b, order='grevlex', domain='QQ')
print(len(G.exprs))
for i in range(4):
  for j in range(i+1,4):
    m = a[i]*b[j]-a[j]*b[i]
    for p in range(1,4):
      r = G.reduce(sp.expand(m**p))[1]
      if r==0:
        print(i,j,'power',p); break
    else: print(i,j,'not in up to 3')
cs = sp.symbols('c0:%d'%len(gens))
for i in range(4):
  for j in range(i+1,4):
    m = a[i]*b[j]-a[j]*b[i]
    expr = sp.expand(m - sum(c*g for c,g in zip(cs,gens)))
    eqs = sp.Poly(expr, *a, *b).coeffs()
    sol = sp.solve(eqs, cs, dict=True)
    print(i,j, sol)
