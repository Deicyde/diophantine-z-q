# Fricke identity in theta constants: a=th00(16t), b=th10(16t), p=th00(8t), r=th10(8t), s^2=th01(8t)^2=a^2-b^2
import sympy as sp
a,b,p,r=sp.symbols('a b p r')
x=2*a/b; y=-2*p*r/b**2
xp=2+4*r/(p-r); yp=-4*(a**2-b**2)/(p-r)**2
lam=(4-y)/(x-2)            # slope for T + (-P), T=(2,-4), -P=(x,-y)
x3=lam**2-2-x
y3=lam*(2-x3)+4
G=sp.groebner([p**2-a**2-b**2, r**2-2*a*b],p,r,a,b,order='lex')
for name,e in [('x',x3-xp),('y',y3-yp),('curveP',y**2-x**3-4*x),('curveP2',yp**2-xp**3-4*xp)]:
    num=sp.numer(sp.together(e))
    print(name, G.reduce(sp.expand(num))[1]==0)
