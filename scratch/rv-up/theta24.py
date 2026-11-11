"""Independent numerical check of the disc -24 normalization used by h-trust F1 (and N5 L908-927).
Lin-Yang Example 30 (as restated in scratch/h-v14/igusa_check.py) places P_-24 on the curve Y'_5 of period matrices
Omega(z) = z*[[3,5],[5,10]], at x(z) = -6 +- 6 sqrt(-3), where x = eta(z)^6/eta(5z)^6 + 22 + 125 eta(5z)^6/eta(z)^6.
Here: (1) evaluate x at the Heegner points of discriminant -24 on X_0(5) (forms [5,+-4,2], [10,+-4,1]);
(2) evaluate F1's theta expression  j = 3779136 (prod theta_m)^4 / (sum theta_m^8)^5  (ten even characteristics)
directly at Omega(z), and compare with -16/27.  Uses only eta/theta series (no Lin-Yang polynomial, no Baba-Granath).
This checks Lin-Yang's x-value and, given that Omega(z) is the QM point P_-24 (see endo24.py), F1's value at P_-24."""
import mpmath as mp
mp.mp.dps = 40
def eta(z, terms=400):
    q = mp.exp(2j*mp.pi*z)
    p = mp.mpf(1)
    for n in range(1, terms):
        p *= (1 - q**n)
    return mp.exp(2j*mp.pi*z/24) * p
def xval(z):
    r = (eta(z)/eta(5*z))**6
    return r + 22 + 125/r
def theta(a, b, Om, N=30):
    s = mp.mpc(0)
    for n1 in range(-N, N+1):
        for n2 in range(-N, N+1):
            v = (n1 + mp.mpf(a[0])/2, n2 + mp.mpf(a[1])/2)
            Q = v[0]*v[0]*Om[0][0] + 2*v[0]*v[1]*Om[0][1] + v[1]*v[1]*Om[1][1]
            s += mp.exp(1j*mp.pi*Q + 1j*mp.pi*(v[0]*b[0] + v[1]*b[1]))
    return s
even = [(a, b) for a in [(0,0),(0,1),(1,0),(1,1)] for b in [(0,0),(0,1),(1,0),(1,1)] if (a[0]*b[0]+a[1]*b[1]) % 2 == 0]
assert len(even) == 10
target = -6 + 6*mp.sqrt(-3)
for (A, B, C) in [(5, 4, 2), (5, -4, 2), (10, 4, 1), (10, -4, 1)]:
    assert B*B - 4*A*C == -24 and A % 5 == 0
    z = (-B + mp.sqrt(-24))/(2*A)
    xv = xval(z)
    Om = [[3*z, 5*z], [5*z, 10*z]]
    th = [theta(a, b, Om) for a, b in even]
    P = mp.fprod(th); S = mp.fsum([t**8 for t in th])
    jv = 3779136 * P**4 / S**5
    print(f"form [{A},{B},{C}]: x = {mp.nstr(xv, 20)}; x^2+12x+144 = {mp.nstr(abs(xv**2+12*xv+144), 5)};"
          f" j_theta = {mp.nstr(jv, 25)}; |j_theta + 16/27| = {mp.nstr(abs(jv + mp.mpf(16)/27), 5)}")
