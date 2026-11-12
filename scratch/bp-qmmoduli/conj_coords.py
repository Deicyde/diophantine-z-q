import sympy as sp
exec(open('order_table.py').read().split('print("---- dag')[0].split('for k,c in enumerate(cs)')[0])
n = sp.symbols('n0:4')
x = [sum(n[k]*E[k][c] for k in range(4)) for c in range(4)]
def nrd(v): return v[0]**2 - a*v[1]**2 - b*v[2]**2 + a*b*v[3]**2
def conj(v): return (v[0], -v[1], -v[2], -v[3])
def inv(w):
    N = nrd(w); return tuple(sp.Rational(1)*c/N for c in conj(w))
for name,w in [("w2",(1,1,1,0)),("w3",(0,0,1,0)),("mu",(0,0,2,1))]:
    wi = inv(w)
    print(name, "inv", wi)
    print("  w x w^-1:", [sp.expand(c) for c in coords(mul(mul(w,x),wi))])
    print("  w^-1 x w:", [sp.expand(c) for c in coords(mul(mul(wi,x),w))])
