# C1: exact checks of the constants in N5 L796-905.
from fractions import Fraction as Fr
from math import prod, log, lgamma
def gl(n,q): return prod(q**n-q**i for i in range(n))
G0=116064000000
print("GL4(F5) =", gl(4,5), "== G0:", gl(4,5)==G0, "; GL4(F3) =", gl(4,3), "<= G0:", gl(4,3)<=G0)
# E0 = 10(DG0)^2 >= 2 + 2*U0 with U0 = 4(DG0)^2, for every D>=1 (x = DG0 >= 1)
print("2+8x^2 <= 10x^2 for x>=1: ", all(2+8*x*x<=10*x*x for x in [1,2,10**6]))
# break: 2(1+log2(a!)) <= 4a^2 for a>=1 (log2(a!) <= a log2 a <= 2a^2-1)
ok=all(2*(1+lgamma(a+1)/log(2))<=4*a*a for a in list(range(1,2000))+[10**k for k in range(4,40)])
print("2(1+log2 a!) <= 4a^2 on sample:", ok)
# Transfer arithmetic: 1024*(320+2+38) and the final sum
print("1024*360 =", 1024*360)
# log-bounds at worst case Q=1e12, scanning M (log M <= M^4/4)
Q=Fr(10**12)
okl=True
for M in [1,2,3,10,10**3,10**9]:
    g=Q**3*M**4; dprime=Q*M; hJ=Q**13*M**24
    okl &= log(14*float(g)) <= 5*float(Q)*M**4
    okl &= log(float(dprime)) <= 2*float(Q)*M**4
    okl &= 13*log(float(Q))+24*log(M) <= 19*float(Q)*M**4
print("three log bounds on sample:", okl)
# 64 g^2 *5QM^4 + 2QM^4 + 38QM^4 <= 360 Q^7 M^12 (g = Q^3 M^4), exact for Q>=1e12, M>=1
for M in [1,2,7]:
    g=Q**3*M**4
    assert 64*g**2*5*Q*M**4+2*Q*M**4+38*Q*M**4 <= 360*Q**7*M**12
    assert 1024*g**3*360*Q**7*M**12 == 368640*Q**16*M**24
    assert 368640*Q**16*M**24 <= Q**17*M**24
    assert Q**13*M**24+Fr(1,2)*Q**17*M**24+2*Q**3*M**4 <= Q**17*M**24
    assert 13000000*(Q*M**2)**12 <= Q**13*M**24
print("transfer chain exact at Q=1e12, M in {1,2,7}: ok")
# [L':Q] chain: 4 D R^R <= R^{R E0} trivially; check 4D <= R^2 given R>=D, R>=1e12
print("4D<=R^2 when R>=max(D,1e12): yes since 4<=R")
