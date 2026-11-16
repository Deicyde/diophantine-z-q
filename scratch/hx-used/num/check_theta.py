# hx-used: (Ix) in theta form: for the lattice <1, w>,  th(0;w) / (e^{pi i w/4} th(w/2;w)) = 1 - 2 R(w),
# R(w) = (p(1/2) - p(1/2 + w/8)) / (p(3w/8) - p(1/2 + w/8)),  th = Mathlib's jacobiTheta2, p = wp of <1, w>.
from mpmath import mp, mpc, exp, pi, jtheta
import random
mp.dps = 40
I = mpc(0, 1)
def wp(z, T):
    q = exp(pi*I*T); t2 = jtheta(2, 0, q); t3 = jtheta(3, 0, q)
    return (pi*t2*t3*jtheta(4, pi*z, q)/jtheta(1, pi*z, q))**2 - pi**2/3*(t2**4 + t3**4)
def th(z, T):
    return jtheta(3, pi*z, exp(pi*I*T))
random.seed(7)
worst = 0
for i in range(12):
    w = mpc(random.uniform(-0.5, 0.5), random.uniform(0.6, 2.5))
    R = (wp(0.5, w) - wp(0.5 + w/8, w))/(wp(3*w/8, w) - wp(0.5 + w/8, w))
    lhs = th(0, w)/(exp(pi*I*w/4)*th(w/2, w))
    e = abs(lhs - (1 - 2*R))/abs(lhs)
    worst = max(worst, e)
    print(i, mp.nstr(w, 6), mp.nstr(e, 3))
print('worst', mp.nstr(worst, 3))
