# test closed forms of gz-theta's etaSqExp mod 12
import random
def tdiv(a,c):  # Lean Int./ : T-division? Lean 4 Int `/` is Int.div = ediv (Euclidean? ) -> Lean4 `/` on Int is `Int.div` = T-rounding? Actually HDiv Int is Int.div (ediv since 2023)
    q = a//c if c>0 else -((a)//(-c))
    return q
def emod(a,c): return a - c*tdiv(a,c)
def E(fuel,a,b,c,d):
    if fuel==0 or c==0: return b if a==1 else 6-b
    q=tdiv(a,c); r=emod(a,c)
    assert 0<=r<abs(c)
    return q-3+E(fuel-1,c,d,-r,-(b-q*d))
def X(a,b,c,d): return (a-2*d)*c - b*d*(c*c-1) + 3*d - 3
def Y(a,b,c,d): return (a+d)*c - b*d*(c*c-1) - 3*c
from math import gcd
bad=0; n=0
random.seed(1)
for _ in range(20000):
    c=random.randint(-60,60); d=random.randint(-60,60)
    if gcd(c,d)!=1: continue
    # find a,b with ad-bc=1
    def eg(x,y):
        if y==0: return (1 if x>0 else -1,0)
        s,t=eg(y,x%y); return (t, s-(x//y)*t)
    s,t=eg(d,-c) if True else None
    # want a*d - b*c =1 : a = s', b = -t'
    # solve a*d + b'*(-c) = 1 with b = -b'... use extended gcd on (d,c)
    import sympy
    g,(u,v)=None,(None,None)
    u,v,g = sympy.gcdex(d,c)
    u=int(u); v=int(v)
    if int(g)==-1: u,v=-u,-v
    a=u; b=-v
    k=random.randint(-5,5); a+=k*c; b+=k*d
    assert a*d-b*c==1
    e=E(200,a,b,c,d)%12
    n+=1
    if d%2!=0 and e!=X(a,b,c,d)%12: bad+=1; print("Xfail",a,b,c,d,e,X(a,b,c,d)%12) if bad<5 else None
    if c%2!=0 and e!=Y(a,b,c,d)%12: bad+=1; print("Yfail",a,b,c,d,e,Y(a,b,c,d)%12) if bad<5 else None
print("tested",n,"bad",bad)
