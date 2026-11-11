# R1/R5 checks: exact rational arithmetic, stdlib only, 30 samples each.
from fractions import Fraction as F
from math import isqrt
import random
random.seed(1)
def is_sq(q):
    q=F(q)
    if q<0: return False
    n,d=q.numerator,q.denominator
    return isqrt(n)**2==n and isqrt(d)**2==d
def on_C(x,y,d): return y*y==x**3-d*d*x
ok1=0
for _ in range(30):
    a=random.choice([1,-1])*random.choice([7,15,23,31,39,47,55,71,79,87,95,103,111,119,127])
    s=F(random.randint(-40,40) or 1,random.randint(1,40))
    # R1: d = a(a^2 s^4-1), point x = a(a s^2+1)^2
    d=a*(a*a*s**4-1)
    x=a*(a*s*s+1)**2
    rhs=x**3-d*d*x
    assert is_sq(rhs), (a,s)
    assert is_sq(x/a) and x!=0
    ok1+=1
print("R1 explicit point on C_{a(a^2s^4-1)} with x in aQ*^2:",ok1,"/30")
ok5=0
for _ in range(30):
    u=random.randint(2,200); v=random.randint(1,u-1)
    n=u*v*(u*u-v*v); x=F(n*u,v); y=F(n*n,v*v)
    assert on_C(x,y,n)
    assert is_sq(x/(u*u-v*v))
    ok5+=1
print("R5 point (nu/v, n^2/v^2) on C_{uv(u^2-v^2)}, class u^2-v^2:",ok5,"/30")
