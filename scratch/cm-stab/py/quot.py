import sympy as sp
n=sp.symbols('n0:4'); m=sp.symbols('m0:4')
mc=[m[0]*n[0]+2*m[1]*n[1]+2*m[1]*n[3]-m[2]*n[2]+2*m[3]*n[3],
     m[0]*n[1]+m[1]*n[0]+m[1]*n[2]-m[2]*n[3]+m[3]*n[2],
     m[0]*n[2]-2*m[1]*n[3]+m[2]*n[0]+m[2]*n[2]+2*m[3]*n[1],
     m[0]*n[3]-m[1]*n[2]+m[2]*n[1]+m[2]*n[3]+m[3]*n[0]]
a=(n[0]-n[2]); b=(n[1]-n[3]); c=(m[0]-m[2]); d=(m[1]-m[3])
re = sp.expand((mc[0]-mc[2]) - (a*c-b*d))
im = sp.expand((mc[1]-mc[3]) - (a*d+b*c))
print("re diff /3:", sp.factor(re), "|", sp.expand(re/3))
print("im diff /3:", sp.expand(im/3))
