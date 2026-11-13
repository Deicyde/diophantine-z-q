# check the four step congruences over residues (mod 12), and the y / (x-2)^2 combinations
def X(a,b,c,d): return (a-2*d)*c - b*d*(c*c-1) + 3*d - 3
def Y(a,b,c,d): return (a+d)*c - b*d*(c*c-1) - 3*c
import itertools
M=12
fails={k:0 for k in ['dX','dY','cX','cY']}
for c,d,q,r,bp in itertools.product(range(M),repeat=5):
    if (d*r - c*bp - 1) % M: continue
    a=c*q+r; b=bp+q*d
    lhsX=(q-3+X(c,d,-r,-bp))%M; lhsY=(q-3+Y(c,d,-r,-bp))%M
    if d%2==1 and bp%2==1 and lhsX!=X(a,b,c,d)%M: fails['dX']+=1
    if d%2==1 and r%2==1 and lhsY!=X(a,b,c,d)%M: fails['dY']+=1
    if c%2==1 and bp%2==1 and lhsX!=Y(a,b,c,d)%M: fails['cX']+=1
    if c%2==1 and r%2==1 and lhsY!=Y(a,b,c,d)%M: fails['cY']+=1
print(fails)
# combos for gamma in Gamma0(32): c=32k
bad=0
for a,b,k,d in itertools.product(range(24),repeat=4):
    c=32*k
    Xd=lambda dl: X(a,dl*b,c//dl,d)
    Ey=2*Xd(8)+Xd(16)-Xd(4)-2*Xd(32)
    Ex=2*Xd(2)+Xd(16)-Xd(4)-2*Xd(32)
    if d%2==1 and (Ey%12 or Ex%12): bad+=1
print("combo bad",bad)
