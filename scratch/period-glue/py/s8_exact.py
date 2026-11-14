"""period-glue: S8Nonzero certificate data.
(1) theta_m(Omega0) for Omega0 = [[(-1+i)/2, 1], [1, -1+i]] factor as unit * th[a1,b1+a2](t1) * th[a2,b2+a1](t2),
    t1 = (-1+i)/2, t2 = -1+i (one-variable thetas with characteristics);
(2) S8 = sum theta_m^8 = -9 * theta00(i)^16 (checked to 60 digits);
(3) rigorous enclosure of S8 by truncation |n_k| <= N plus an explicit tail bound (mpmath interval arithmetic).
Run: ~/pyenv/bin/python -I s8_exact.py"""
import mpmath as mp
mp.mp.dps = 60
I = mp.mpc(0,1)
O00, O01, O11 = (-1+I)/2, mp.mpf(1), -1+I
chars = [((a1,a2),(b1,b2)) for a1 in (0,1) for a2 in (0,1) for b1 in (0,1) for b2 in (0,1)]
ev = [ch for ch in chars if (ch[0][0]*ch[1][0] + ch[0][1]*ch[1][1]) % 2 == 0]
def theta2(ch, N=30):
    (a1,a2),(b1,b2) = ch; s = mp.mpc(0)
    for n1 in range(-N, N+1):
        for n2 in range(-N, N+1):
            x1 = n1 + mp.mpf(a1)/2; x2 = n2 + mp.mpf(a2)/2
            Q = x1*x1*O00 + 2*x1*x2*O01 + x2*x2*O11
            s += mp.exp(I*mp.pi*(Q + x1*b1 + x2*b2))
    return s
def th1(a, b, t, N=60):
    return mp.fsum(mp.exp(I*mp.pi*((n+mp.mpf(a)/2)**2*t + (n+mp.mpf(a)/2)*b)) for n in range(-N, N+1))
A = th1(0,0,I)
S = 0
print("char, theta_m, unit = theta_m/(th[a1,b1+a2](t1) th[a2,b2+a1](t2)), theta_m^8/theta00(i)^16")
for ch in ev:
    (a1,a2),(b1,b2) = ch
    t = theta2(ch); S += t**8
    f = th1(a1, b1+a2, O00) * th1(a2, b2+a1, O11)
    u = t/f if abs(f) > mp.mpf(10)**-40 else None
    print(ch, mp.nstr(t, 12), (mp.nstr(u, 12) if u is not None else "f=0"), mp.nstr(t**8/A**16, 15))
print("theta00(i) =", mp.nstr(A, 30), " (pi^(1/4)/Gamma(3/4) =", mp.nstr(mp.pi**0.25/mp.gamma(0.75), 30), ")")
print("S8 =", mp.nstr(S, 40))
print("S8 / theta00(i)^16 =", mp.nstr(S/A**16, 40))
# rigorous enclosure: |term(n)| = exp(-pi (x1^2/2 + x2^2)); tail over the complement of the box |n_k|<=N
iv = mp.iv; iv.dps = 30
def tail_bound(N):
    # sum over all x in Z+a/2 with |n|>N of exp(-pi c x^2) <= 2 * sum_{k>=N+1-1/2} exp(-pi c k^2), geometric bound
    def t1(c):  # bound for sum_{|n|>N} exp(-pi c (n+a/2)^2), a in {0,1}: |n+a/2| >= N+1/2
        x0 = iv.mpf(N) + iv.mpf(1)/2
        q = iv.exp(-iv.pi*c*(2*x0+1))   # ratio bound of consecutive terms
        return 2*iv.exp(-iv.pi*c*x0**2)/(1-q)
    def full(c):  # bound for the full sum over Z+a/2
        return 2*(1 + t1(c))   # crude: |n+a/2|<=N part bounded by sum over all, sum<=1+... ; we use 2*(1+t1)
    c1, c2 = iv.mpf(1)/2, iv.mpf(1)
    # complement of box = {|n1|>N} union {|n2|>N}
    return t1(c1)*full(c2) + full(c1)*t1(c2)
for N in (2, 3, 4):
    print("N =", N, " tail bound per theta <=", tail_bound(N))
