from gsg_enum import *
import itertools
gens={'a':x4,'A':inv(x4),'b':x6,'B':inv(x6)}
def word(w):
    r=(1,0,0,0)
    for ch in w: r=mul(r,gens[ch])
    return r
nbrs=[(0,Fr(1,2),1,Fr(-1,2)),(0,Fr(1,2),1,Fr(1,2)),(0,Fr(7,2),3,Fr(-1,2)),(0,Fr(7,2),3,Fr(1,2))]
found={}
for L in range(1,4):
    for w in itertools.product('aAbB',repeat=L):
        s=word(w)
        u=mul(mul(inv(s),y),s)
        u=tuple(Fr(t) for t in u)
        for k,nb in enumerate(nbrs):
            if u==tuple(Fr(t) for t in nb) and k not in found:
                found[k]=(''.join(w),s,nrd(s))
for k in found: print(k,nbrs[k],found[k])
# step B: F = {x4^k j x4^-k}
j=(0,0,1,0)
for k in range(4):
    s=word('a'*k); print(k,[str(t) for t in mul(mul(s,j),inv(s))])
print('x4 y x4^-1 =',mul(mul(x4,y),inv(x4)))
print('x2=2 x6 x4^-1',[str(t) for t in tuple(2*t for t in mul(x6,inv(x4)))])
