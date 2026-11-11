# C2: square class of R0 = eta*F(t)/(t-1)^8 at the slopes of Proposition AP.
# t = u/v with u - b v prime for b in patternShifts = contactSet ∪ {1}; and t3 = -10.
from fractions import Fraction as F
from sympy import factorint, isprime
C=[0,-15,-20,-24,-30,-60]
def sqf(x):
    x=F(x); n=x.numerator*x.denominator; s=-1 if n<0 else 1; r=1
    for p,e in factorint(abs(n)).items():
        if e%2: r*=p
    return s*r
def Fc(t): 
    r=F(1)
    for c in C: r*=(t-c)
    return r
def R0class(t):
    R=Fc(t)/(t-1)**8
    return sqf(abs(R))   # eta chosen so R0>0
print("t3=-10: F(-10) =",Fc(F(-10)),"class of |R0| =",R0class(F(-10)))
found=0
for v in range(1,60):
    for u in range(62*v,62*v+3000):
        if all(isprime(abs(u-b*v)) for b in C+[1]):
            t=F(u,v); cl=R0class(t); prod=1
            for c in C: prod*=(u-c*v)
            assert cl==sqf(prod)
            ms=[m for m in [1,2,3,5,6,7,10,14,15,21,30,35,42,70,105,210] if sqf(m*cl)%8==7]
            if found<8: print("u,v=",u,v,"class=",cl,"omega=",len(factorint(cl)),"m with sqf(m*R0)=7 mod 8:",ms[:4])
            found+=1
            break
print("slopes found:",found,"; class(R0) = prod of the six primes u-cv in every case")
