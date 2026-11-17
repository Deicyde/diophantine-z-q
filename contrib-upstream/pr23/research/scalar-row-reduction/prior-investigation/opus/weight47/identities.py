"""Symbolic check of the R-inverse weight circuit (order 47, and order 46 variant)."""
import sympy as sp
t,A=sp.symbols('t A',positive=True)
roots=[0,sp.Rational(1,49),sp.Rational(1,50),sp.Rational(1,2450),sp.Rational(32,1225)]
F=sp.prod([t-r for r in roots])
delta=98*t-1
q1=A*(A*delta)**4/F; E=q1*delta**2
e=(A*delta)**5/F
assert sp.simplify(q1-e/delta)==0 and sp.simplify(E-e*delta)==0
q1cube=q1**3
R=1/E                      # gate: E*R = 1
q5=q1cube*E/R              # gate: R*q5 = q1cube*E
q11=q5**2/R                # gate: R*q11 = q5^2
q12=q11**2/R               # gate: R*q12 = q11^2
mixedHigh=q12**2           # gate: mixedHigh = q12^2
q47=mixedHigh**2/R         # gate: R*q47 = mixedHigh^2
checks={'q5':(q5,e**5/delta),'q11':(q11,e**11/delta),'q12':(q12,e**23/delta),
        'mixedHigh':(mixedHigh,e**46/delta**2),'q47':(q47,e**93/delta**3)}
for k,(a,b) in checks.items():
    assert sp.cancel(a/b)==1,k; print(k,'ok')
# order 46 variant on the cube-reuse chain: q46*q1 = mixedHigh^2
assert sp.cancel((mixedHigh**2/q1)/(e**91/delta**3))==1; print('q46 = mixedHigh^2/q1 = e^91/delta^3 ok')
# normalization: factor 1 + R*(X/(delta^(m+1) R^m))^2 with X = delta^k D gives e^(2m-1) delta^(2k-3) D^2
m,k,D=47,0,sp.Symbol('D')
Rsem=F/(A**5*delta**6)
lhs=Rsem*((delta**k*D)/(delta**(m+1)*Rsem**m))**2
assert sp.cancel(lhs/(q47*D**2))==1; print('order-47 factor = 1 + R(D/(delta^48 R^47))^2, i.e. semantic test D (k=0)')
lhs1=Rsem*((delta*D)/(delta**(12+1)*Rsem**12))**2
assert sp.cancel(lhs1/(q12*D**2))==1; print('order-12 factor unchanged (k=1)')
