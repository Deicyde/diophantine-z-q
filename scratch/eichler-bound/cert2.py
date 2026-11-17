import sympy as sp
a=sp.symbols('a0:4'); b=sp.symbols('b0:4'); n=sp.symbols('n0:4')
def mul(n,m):
    return [m[0]*n[0]+2*m[1]*n[1]+2*m[1]*n[3]-m[2]*n[2]+2*m[3]*n[3],
            m[0]*n[1]+m[1]*n[0]+m[1]*n[2]-m[2]*n[3]+m[3]*n[2],
            m[0]*n[2]-2*m[1]*n[3]+m[2]*n[0]+m[2]*n[2]+2*m[3]*n[1],
            m[0]*n[3]-m[1]*n[2]+m[2]*n[1]+m[2]*n[3]+m[3]*n[0]]
def conj(n): return [n[0]+n[2],-n[1],-n[2],-n[3]]
def nrd(n): return n[0]**2+n[0]*n[2]+n[2]**2-2*(n[1]**2+n[1]*n[3]+n[3]**2)
X=[sp.expand(x) for x in mul(conj(list(a)),list(b))]
Y=[sp.expand(x) for x in mul(list(a),conj(list(b)))]
gens=X+Y
cs=sp.symbols('c0:8')
for i in range(4):
  for j in range(i+1,4):
    m=6*(a[i]*b[j]-a[j]*b[i])
    expr=sp.expand(m-sum(c*g for c,g in zip(cs,gens)))
    sol=sp.solve(sp.Poly(expr,*a,*b).coeffs(),cs,dict=True)[0]
    sol={c:sol.get(c,c).subs({cc:0 for cc in cs}) for c in cs}
    print(i,j,[sol[c] for c in cs])
# Frob: (conj(pi) z pi - nrd(pi) conj z)/l
I=[0,1,0,0]; J=[-1,0,2,0]
for pi,l in [(I,2),(J,3)]:
    d=[sp.expand((x-y)/l) for x,y in zip(mul(mul(conj(pi),list(n)),pi),[nrd(pi)*x for x in conj(list(n))])]
    print('frob',l,d)
print('comm', [sp.expand(x-y) for x,y in zip(mul(list(a),list(b)),mul(list(b),list(a)))])
