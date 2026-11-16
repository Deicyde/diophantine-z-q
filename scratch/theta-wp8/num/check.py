# Numeric check of the theta-wp8 proof chain (mpmath, 40 digits).
import mpmath as mp, random
mp.mp.dps = 40
def th(z, w, N=60):  # Mathlib jacobiTheta2 z w = sum exp(2 pi i n z + pi i n^2 w)
    return mp.fsum(mp.exp(2j*mp.pi*n*z + 1j*mp.pi*n*n*w) for n in range(-N, N+1))
def wp(z, w, N=60):
    # wp for lattice <1,w> via row sums: sum_n pi^2/sin^2(pi(z-n w)) - const; use differences only
    s = mp.fsum(mp.pi**2/mp.sin(mp.pi*(z-n*w))**2 for n in range(-N, N+1))
    return s
random.seed(1)
for _ in range(4):
    w = mp.mpc(random.uniform(-0.5,0.5), random.uniform(0.6,1.5))
    s = lambda z: th(z + (1+w)/2, w)
    a, b, c = mp.mpf(1)/2, 3*w/8, mp.mpf(1)/2 + w/8
    wr = (wp(a,w)-wp(c,w))/(wp(b,w)-wp(c,w))
    lhs = th(0,w)/(mp.exp(mp.pi*1j*w/4)*th(w/2,w))
    R = s(a-c)*s(a+c)*s(b)**2/(s(a)**2*s(b-c)*s(b+c))
    R2 = th(mp.mpf(1)/2+3*w/8,w)*th(mp.mpf(1)/2+5*w/8,w)*th(mp.mpf(1)/2+7*w/8,w)**2/(th(w/2,w)**2*th(3*w/4,w)*th(w,w))
    # K constancy at random u
    Ks = [ (wp(u,w)-wp(c,w))*s(u)**2/(s(u-c)*s(u+c)) for u in [mp.mpc(random.random(),random.random()) for _ in range(3)]]
    print(mp.nstr(abs(lhs-(1-2*wr)),5), mp.nstr(abs(wr-R),5), mp.nstr(abs(R-R2),5), [mp.nstr(abs(k-Ks[0]),5) for k in Ks], mp.nstr(Ks[0],8),
          mp.nstr(abs(th(0,w)-mp.exp(mp.pi*1j*w/4)*th(w/2,w)-th(mp.mpf(1)/2,w/4)),5))
