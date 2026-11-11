"""Sample check of twelve_mul_ratHeight_le: 12 h(u) <= h(J(u)) + 450, J = -57600 F^2/G^6 (N5 L381-383, L510),
and of the cancellation c = gcd(57600 F_h(a,b)^2, G_h(a,b)^6) | C0. 30 inputs incl. the contact values."""
from fractions import Fraction as Fr
from math import gcd, log
import random
def h(q): q = Fr(q); return log(max(abs(q.numerator), q.denominator))
def J(u): F = u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60); G = 7*u*u+300*u+3600; return Fr(-57600)*F*F/G**6
C0 = (57600*3**7)*(57600*104976000000**7)
random.seed(1)
us = [Fr(c) for c in [0,-15,-20,-24,-30,-60]] + [Fr(-1,2), Fr(-45,2), Fr(-150,7), Fr(1,10**6), Fr(10**9,7)]
us += [Fr(random.randint(-10**6,10**6), random.randint(1,10**6)) for _ in range(19)]
worst = -1e9
for u in us:
    a, b = u.numerator, u.denominator
    Fh = a*(a+15*b)*(a+20*b)*(a+24*b)*(a+30*b)*(a+60*b); Gh = 7*a*a+300*a*b+3600*b*b
    c = gcd(57600*Fh*Fh, Gh**6); assert C0 % c == 0
    slack = 12*h(u) - h(J(u)); worst = max(worst, slack)
    assert slack <= 450
print(len(us), 'samples; max of 12h(u)-h(J(u)) =', round(worst, 3), '(bound 450); all cancellations divide C0')
