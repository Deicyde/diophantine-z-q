# Descent data for the CM3 (w^2=-3) and CM24 (w^2=-6) orbits; base points j and mu=2j+k.
from gsg_enum import mul, inv, nrd, form, inO
from fractions import Fraction as Fr
import itertools
x4=(1,1,1,0); x6=(Fr(-3,2),0,Fr(1,2),0)
gens={'a':x4,'A':inv(x4),'b':x6,'B':inv(x6)}
def word(w):
    r=(1,0,0,0)
    for ch in w: r=mul(r,gens[ch])
    return r
def pts(N, base, bound):
    # pure w in O with nrd w = N (w^2=-N), <w,base>/N in (0,bound]
    out=[]
    for c2 in range(-8*bound,8*bound+1):
      for B2 in range(-16*bound,16*bound+1):
        for D2 in range(-8*bound,8*bound+1):
            w=(0,Fr(B2,2),Fr(c2,2),Fr(D2,2))
            if nrd(w)!=N or not inO(w): continue
            ip=form(w,base)
            if 0<ip<=bound*N: out.append((ip/N,w))
    return sorted(out)
for N,base in ((3,(0,0,1,0)),(6,(0,0,2,1))):
    P=pts(N,base,4)
    from collections import Counter
    print('N',N,'count by cosh',sorted(Counter(p[0] for p in P).items())[:8])
    vals=sorted(set(p[0] for p in P))
    nb=[w for c,w in P if c==vals[1]] if len(vals)>1 else []
    print(' nearest neighbours cosh',vals[1] if len(vals)>1 else None,[tuple(map(str,w)) for w in nb])
    # words s with s^-1 base s = neighbour
    for u in nb:
        for L in range(1,4):
            done=False
            for w in itertools.product('aAbB',repeat=L):
                s=word(w); t=mul(mul(inv(s),base),s)
                if tuple(Fr(x) for x in t)==tuple(Fr(x) for x in u):
                    print('   ',tuple(map(str,u)),'=',''.join(w),'^-1 base',''.join(w)); done=True; break
            if done: break
