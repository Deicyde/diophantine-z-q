# hx-used: the sigma/theta_1 form of R and the resulting theta identity (exploration).
from mpmath import mp, mpc, exp, pi, jtheta
mp.dps = 40
I = mpc(0, 1)
def wp(z, T):
    q = exp(pi*I*T); t2 = jtheta(2, 0, q); t3 = jtheta(3, 0, q)
    return (pi*t2*t3*jtheta(4, pi*z, q)/jtheta(1, pi*z, q))**2 - pi**2/3*(t2**4 + t3**4)
w = mpc('0.13', '1.21')
q = exp(pi*I*w)
t1 = lambda z: jtheta(1, pi*z, q)
t2 = lambda z: jtheta(2, pi*z, q)
a, b, c = mpc(0.5), 3*w/8, 0.5 + w/8
R = (wp(a, w) - wp(c, w))/(wp(b, w) - wp(c, w))
Rs = (t1(a-c)*t1(a+c)/t1(a)**2)/(t1(b-c)*t1(b+c)/t1(b)**2)
print('R vs sigma form', abs(R - Rs))
Rt = -t1(w/8)**2*t1(3*w/8)**2/(t2(0)**2*t2(w/4)*t2(w/2))
print('R vs simplified', abs(R - Rt))
print('1-2R vs th3/th2', abs(1 - 2*R - jtheta(3, 0, q)/jtheta(2, 0, q)))
