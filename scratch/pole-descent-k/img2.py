# 2-adic image of C_n: y^2 = x(x-n)(x+n) under P -> (x, x-n), for n in classes of Q_2^*/Q_2^*2
import random
from fractions import Fraction as F
def v2(q):
    q=F(q); k=0; a,b=q.numerator,q.denominator
    while a%2==0: a//=2;k+=1
    while b%2==0: b//=2;k-=1
    return k,(a*b)%8
def cls(q):
    k,u=v2(q); return (k%2,u)
def issq(q):
    k,u=v2(q); return k%2==0 and u==1
rng=random.Random(1)
for n in [1,3,5,7,2,6,10,14]:
    img=set()
    for t in range(200000):
        k=rng.randrange(-8,9)
        x=F(rng.randrange(-2**12,2**12),rng.randrange(1,2**6,2))*F(2)**k
        if x in (0,n,-n): continue
        if issq(x*(x-n)*(x+n)): img.add((cls(x),cls(x-n)))
    for P in [(F(0),),(F(n),),(F(-n),)]:
        pass
    print(n,len(img),sorted(img))
