# Ligozat orders of eta quotients on Gamma0(32); search even-exponent quotients for x, x+2, x-2, x±2i
from fractions import Fraction as Fr
from math import gcd
import itertools
N=32; D=[1,2,4,8,16,32]
def ords(r):
    return {d: Fr(N,24)*sum(Fr(gcd(d,dl)**2*r[i], gcd(d,N//d)*d*dl) for i,dl in enumerate(D)) for d in D}
# targets (orders at d = 1,2,4,8,16,32): cusp images: 0->(2,-4),1/2->(2,4),±1/4->(-2,∓4i),±1/8->(∓2i,0),1/16->(0,0)
# x has double zero at 1/16 (d=16), double pole at inf (d=32)
targets={'x':{1:0,2:0,4:0,8:0,16:2,32:-2},'x+2':{1:0,2:0,4:1,8:0,16:0,32:-2},'x-2':{1:1,2:1,4:0,8:0,16:0,32:-2}}
for name,t in targets.items():
    sols=[]
    for r in itertools.product(range(-8,9),repeat=6):
        if sum(r)!=0: continue
        o=ords(r)
        if all(o[d]==t[d] for d in D): sols.append(r)
    print(name, sols[:10])
