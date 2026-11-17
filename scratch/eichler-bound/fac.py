import sympy as sp
n=sp.symbols('n0:4')
def mul(n,m):
    return [m[0]*n[0]+2*m[1]*n[1]+2*m[1]*n[3]-m[2]*n[2]+2*m[3]*n[3],
            m[0]*n[1]+m[1]*n[0]+m[1]*n[2]-m[2]*n[3]+m[3]*n[2],
            m[0]*n[2]-2*m[1]*n[3]+m[2]*n[0]+m[2]*n[2]+2*m[3]*n[1],
            m[0]*n[3]-m[1]*n[2]+m[2]*n[1]+m[2]*n[3]+m[3]*n[0]]
def conj(n): return [n[0]+n[2],-n[1],-n[2],-n[3]]
I=[0,1,0,0]; J=[-1,0,2,0]
print('left i', [sp.expand(x/-2) for x in mul(conj(I),list(n))])
print('left j', [sp.expand(x/3) for x in mul(conj(J),list(n))])
print('right i', [sp.expand(x/-2) for x in mul(list(n),conj(I))])
print('right j', [sp.expand(x/3) for x in mul(list(n),conj(J))])
