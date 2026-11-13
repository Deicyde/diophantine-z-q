exec(open('cusps.py').read().split("for name")[0])
def add(P,Q):
    if P is None: return Q
    if Q is None: return P
    (x1,y1),(x2,y2)=P,Q
    if abs(x1-x2)<1e-9:
        if abs(y1+y2)<1e-9: return None
        l=(3*x1*x1+4)/(2*y1)
    else: l=(y1-y2)/(x1-x2)
    x3=l*l-x1-x2; y3=-(l*(x3-x1)+y1)
    return (x3,y3)
def neg(P): return None if P is None else (P[0],-P[1])
T=(2+0j,-4+0j)
for t in [0.1+0.3j, -0.13+0.21j, 0.05+0.25j]:
    W=-1/(32*t)
    P=xy(t); Q=xy(W)
    print('P',P,'Q',Q)
    print(' P+Q', add(P,Q), ' Q-P', add(Q,neg(P)))
    e=lambda z:eta(z)
    X2=8*e(2*t)*e(16*t)**2/(e(t)**2*e(8*t))+2
    print(' x(Wt) vs formula', Q[0], X2)
