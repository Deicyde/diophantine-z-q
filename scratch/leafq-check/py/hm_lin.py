import sympy as sp
from gsg_sym import mul
R=sp.Rational
b,c,d=sp.symbols('b c d')
v=(0,b,c,d)
def form(v,u): return -2*v[1]*u[1]+3*v[2]*u[2]-6*v[3]*u[3]
x4=(1,1,1,0); x4i=(R(1,2),R(-1,2),R(-1,2),0)
x6=(R(-3,2),0,R(1,2),0); x6i=(R(-1,2),0,R(-1,6),0); mu=(0,0,2,1); mui=(0,0,R(-1,3),R(-1,6))
def W(*xs):
    r=(1,0,0,0)
    for x in xs: r=mul(r,x)
    return tuple(sp.nsimplify(t) for t in r)
j=(0,0,1,0)
lists={3:(j,[('a',W(x4),W(x4i)),('A',W(x4i),W(x4)),('ab',W(x4,x6),W(x6i,x4i)),('AB',W(x4i,x6i),W(x6,x4)),('abb',W(x4,x6,x6),W(x6i,x6i,x4i)),('ABB',W(x4i,x6i,x6i),W(x6,x6,x4))]),
       6:(mu,[('b',W(x6),W(x6i)),('B',W(x6i),W(x6)),('aBB',W(x4,x6i,x6i),W(x6,x6,x4i)),('bm',W(x6,mu),W(mui,x6i))])}
for N,(base,L) in lists.items():
    print('N',N)
    for name,s,si in L:
        assert [sp.simplify(t) for t in mul(s,si)]==[1,0,0,0]
        w=mul(mul(s,v),si)
        val=sp.expand(form(w,base)); diff=sp.expand(val-form(v,base))
        print(' ',name,'s=',s,'si=',si,'form=',val,' diff=',diff)
