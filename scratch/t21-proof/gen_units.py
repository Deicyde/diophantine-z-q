from fractions import Fraction as F
from itertools import product
half=F(1,2)
units=[]
for s in product([-1,0,1],repeat=4):
    if sum(x*x for x in s)==1: units.append(tuple(F(x) for x in s))
for s in product([half,-half],repeat=4): units.append(s)
def hc(q): return (q[0]+q[3], q[1]-q[3], q[2]-q[3], 2*q[3])
L=[tuple(int(c) for c in hc(u)) for u in units]
print("[" + ", ".join(f"⟨{a},{b},{c},{d}⟩" for a,b,c,d in L) + "]")
# partners: beta_t = x + y omega + 4 q
for s in product([1,-1],repeat=3):
    om=(F(1+s[2],2),F(s[0]-s[2],2),F(s[1]-s[2],2),F(s[2]))
    for t in product([0,1],repeat=3):
        if t==(0,0,0): continue
        b=(1,2*t[0],2*t[1],2*t[2])
        for x in range(4):
            for y in range(4):
                d=[b[i]-(x if i==0 else 0)-y*om[i] for i in range(4)]
                if all(di.denominator==1 and di.numerator%4==0 for di in d):
                    print(s,t,x,y,[int(di)//4 for di in d])
