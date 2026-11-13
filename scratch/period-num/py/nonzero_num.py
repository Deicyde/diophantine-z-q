"""period-num: numerics behind part_nonzero.lean (S8Nonzero). Pure python3 (floats).
Checks: Omega(sqrt2+i); the splitting theta_m = c_m * th1(a0,b0+a1,w1) * th1(a1,b1+a0,w2);
the factorization S = (Z0^8+Z1^8+T^8)(P0^8+P1^8+Q^8); the bounds used in the Lean proof."""
import cmath, math
from num0 import Omega, theta, chars  # noqa
s2=math.sqrt(2); w1=(-1+1j)/2; w2=-1+1j
def th1(a,b,w,N=30):
    return sum(cmath.exp(1j*math.pi*(n+a/2)**2*w + 1j*math.pi*(n+a/2)*b) for n in range(-N,N+1))
O=Omega(s2+1j)
print("Omega0 =", O)
S=0
for ch in chars:
    (a0,a1),(b0,b1)=ch
    t=theta(ch,O); u=cmath.exp(-1j*math.pi*a0*a1/2)*th1(a0,b0+a1,w1)*th1(a1,b1+a0,w2)
    print(ch, "theta =", t, " split =", u, " |diff| =", abs(t-u)); S+=t**8
Z0,Z1,T=th1(0,0,w1),th1(0,1,w1),th1(1,0,w1); P0,P1,Q=th1(0,0,w2),th1(0,1,w2),th1(1,0,w2)
F1=Z0**8+Z1**8+T**8; F2=P0**8+P1**8+Q**8
print("S =", S, " F1*F2 =", F1*F2)
print("Z0 =",Z0," Z1 =",Z1," Re Z0^8 =",(Z0**8).real," Re Z1^8 =",(Z1**8).real)
print("T*e^{i pi/8} =",T*cmath.exp(1j*math.pi/8)," T^8 =",T**8)
print("P0 =",P0," P1 =",P1," Q*e^{i pi/4} =",Q*cmath.exp(1j*math.pi/4))
print("F1 =",F1," F2 =",F2)
q=math.exp(-math.pi/2); r=math.exp(-math.pi)
print("q = e^{-pi/2} =",q," in (0.135,0.227):",0.135<q<0.227)
print("tail bound r^2/(1-r) =",r*r/(1-r)," <= 1/380:",r*r/(1-r)<=1/380)
print("|Z0-(1-2iq)| =",abs(Z0-(1-2j*q))," |Z1-(1+2iq)| =",abs(Z1-(1+2j*q)))
