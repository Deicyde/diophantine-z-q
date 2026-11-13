"""period-glue: Omega(sqrt2+i) exactly, the ten even theta constants, Im Omega eigenvalues, and tail sizes.
Run: ~/pyenv/bin/python -I s8_value.py"""
import sympy as sp, mpmath as mp
mp.mp.dps = 40
R = sp.Rational; s2 = sp.sqrt(2); I = sp.I
basis = [(1,0,0,0), (0,1,0,0), (R(1,2),0,R(1,2),0), (0,R(1,2),0,R(1,2))]
def iota(x):
    x0,x1,x2,x3 = x
    Mi = sp.Matrix([[s2,0],[0,-s2]]); Mj = sp.Matrix([[0,-3],[1,0]])
    return x0*sp.eye(2) + x1*Mi + x2*Mj + x3*Mi*Mj
t0 = s2 + I; v = sp.Matrix([t0, 1])
cols = [iota(b)*v for b in basis]
Pinv = sp.Matrix([[-2,-1],[-1,-1]])
E = sp.Matrix.hstack(cols[0], cols[1]); F = sp.Matrix.hstack(cols[2], cols[3]) * Pinv
Om = sp.simplify(F.inv()*E)
Om = Om.applyfunc(lambda z: sp.nsimplify(sp.radsimp(sp.expand(z))))
print("Omega(sqrt2+i) =", Om)
print("Re =", Om.applyfunc(lambda z: sp.simplify(sp.re(z))))
Y = Om.applyfunc(lambda z: sp.simplify(sp.im(z)))
print("Im =", Y, " eigen:", [sp.N(e, 20) for e in Y.eigenvals()])
Omn = mp.matrix([[mp.mpc(sp.N(sp.re(Om[r,c]),50), sp.N(sp.im(Om[r,c]),50)) for c in range(2)] for r in range(2)])
chars = [((a1,a2),(b1,b2)) for a1 in (0,1) for a2 in (0,1) for b1 in (0,1) for b2 in (0,1)]
ev = [ch for ch in chars if (ch[0][0]*ch[1][0] + ch[0][1]*ch[1][1]) % 2 == 0]
def theta(ch, N):
    (a1,a2),(b1,b2) = ch; s = mp.mpc(0)
    for n1 in range(-N, N+1):
        for n2 in range(-N, N+1):
            x1 = n1 + mp.mpf(a1)/2; x2 = n2 + mp.mpf(a2)/2
            Q = x1*x1*Omn[0,0] + 2*x1*x2*Omn[0,1] + x2*x2*Omn[1,1]
            s += mp.exp(1j*mp.pi*(Q + x1*b1 + x2*b2))
    return s
S = 0
for ch in ev:
    th = theta(ch, 12); th2 = theta(ch, 2); th1 = theta(ch, 1)
    S += th**8
    print(ch, "theta =", mp.nstr(th, 15), " |theta^8| =", mp.nstr(abs(th**8), 8), " err(N=1) =", mp.nstr(abs(th-th1), 3), " err(N=2) =", mp.nstr(abs(th-th2),3))
print("S8 =", mp.nstr(S, 20))
