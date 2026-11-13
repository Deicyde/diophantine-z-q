"""period-map: weight-8 check of G8 = S/dF^4 on the order-4 elliptic generator 1+i+j of Gamma* (nrd 2, fixes sqrt2+i),
and the orders in PSL2 of the three elliptic generators. Run: ~/pyenv/bin/python -I gen_check.py (imports al_weight's defs)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'al_weight.py')).read().split("print(\"check iota")[0])
def qmul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    return (a1*a2 + 2*b1*b2 - 3*c1*c2 + 6*d1*d2, a1*b2 + b1*a2 + 3*(c1*d2 - d1*c2),
            a1*c2 + c1*a2 + 2*(b1*d2 - d1*b2), a1*d2 + d1*a2 + b1*c2 - c1*b2)
def nrd(x): a,b,c,d = x; return a*a - 2*b*b + 3*c*c - 6*d*d
dF = lambda t: (t-3)*(t+1)
for name, x in {"1+i+j (nrd 2)": (1,1,1,0)}.items():
    a,b,c,d = mob(x); det = a*d-b*c
    t0 = mp.sqrt(2)+1j; print(name, "nrd", nrd(x), "fixes sqrt2+i:", mp.nstr(abs((a*t0+b)/(c*t0+d)-t0),5))
    for t in [mp.mpc('0.3','1.1'), mp.mpc('-0.7','0.9')]:
        gt = (a*t+b)/(c*t+d); S1,P1 = SP(t); S2,P2 = SP(gt); r = abs(dF(gt)/dF(t))
        print(f"   t={mp.nstr(t,4)}: ratio = {mp.nstr(abs(S2/S1)/r**4/abs(c*t+d)**8*det**4,12)}")
# PSL orders: smallest n with x^n in Q (scalar)
for name, x in {"mu=2j+ij": (0,0,2,1), "1+i+j": (1,1,1,0), "j": (0,0,1,0), "(1+j)/2": (R(1,2),0,R(1,2),0), "j*(1+j)/2": qmul((0,0,1,0),(R(1,2),0,R(1,2),0))}.items():
    y = x; n = 1
    while not (y[1]==0 and y[2]==0 and y[3]==0) and n < 13:
        y = qmul(y, x); n += 1
    print(name, "order in PSL2:", n)
