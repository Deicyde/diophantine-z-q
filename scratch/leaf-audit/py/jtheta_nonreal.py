# leaf-audit: evaluate PkgI1.jNum/jDen (Omega tau) exactly as defined in ZInQKernel/OneProof/H/LPrefix.lean
# (thetaConst, evenChars, thetaSum8, thetaProd2, Omega = (F0mat*Pinv)^-1 * Emat, iota with Mi=diag(sqrt2,-sqrt2),
# Mj=[[0,-3],[1,0]], oBasis = 1, i, (1+j)/2, (i+ij)/2) at a few tau, to test whether j_theta takes non-real values.
import mpmath as mp
mp.mp.dps = 40
s2 = mp.sqrt(2)
Mi = mp.matrix([[s2, 0], [0, -s2]])
Mj = mp.matrix([[0, -3], [1, 0]])
I2 = mp.eye(2)
def iota(re, a, b, c):  # x = re + a i + b j + c ij
    return re*I2 + a*Mi + b*Mj + c*(Mi*Mj)
oB = [(1,0,0,0), (0,1,0,0), (mp.mpf(1)/2,0,mp.mpf(1)/2,0), (0,mp.mpf(1)/2,0,mp.mpf(1)/2)]
def latVec(x, t):
    return iota(*x) * mp.matrix([t, 1])
def Omega(t):
    E = mp.matrix(2, 2); F0 = mp.matrix(2, 2)
    for c in range(2):
        v = latVec(oB[c], t); w = latVec(oB[c+2], t)
        for r in range(2):
            E[r, c] = v[r]; F0[r, c] = w[r]
    Pinv = mp.matrix([[-2, -1], [-1, -1]])
    return (F0*Pinv)**-1 * E
def theta(m, Om, R=12):
    a, b = m; tot = mp.mpc(0)
    for n0 in range(-R, R+1):
        for n1 in range(-R, R+1):
            v = [n0 + mp.mpf(a[0])/2, n1 + mp.mpf(a[1])/2]
            q = sum(v[i]*Om[i, j]*v[j] for i in range(2) for j in range(2))
            l = v[0]*b[0] + v[1]*b[1]
            tot += mp.exp(mp.pi*1j*q + mp.pi*1j*l)
    return tot
chars = [((a0,a1),(b0,b1)) for a0 in (0,1) for a1 in (0,1) for b0 in (0,1) for b1 in (0,1)
         if (a0*b0 + a1*b1) % 2 == 0]
assert len(chars) == 10
def jtheta(t):
    Om = Omega(t)
    sym = max(abs(Om[0,1]-Om[1,0]), 0)
    imO = mp.matrix([[Om[i,j].imag for j in range(2)] for i in range(2)])
    th = [theta(m, Om) for m in chars]
    S8 = sum(x**8 for x in th); P2 = mp.fprod([x**2 for x in th])
    return 3779136*P2**2 / S8**5, S8**5, sym, mp.det(imO), imO[0,0]
for t in [mp.mpc(0.3, 1.1), mp.mpc(0.1, 0.9), mp.mpc(-0.4, 1.3), mp.mpc(0.0, 1.0)*mp.sqrt(3)]:
    j, den, sym, d, i00 = jtheta(t)
    print("tau =", mp.nstr(t, 8), " j_theta =", mp.nstr(j, 15), " |jDen| =", mp.nstr(abs(den), 6),
          " |Om12-Om21| =", mp.nstr(sym, 3), " det Im Om =", mp.nstr(d, 6), " Im Om00 =", mp.nstr(i00, 6))
print("validation at pkg-I1's CM points (expected 0 at sqrt2+i, -16/27 = -0.592592... at i*sqrt(9+6sqrt2)):")
for t in [s2 + 1j, 1j*mp.sqrt(9 + 6*s2)]:
    j, den, sym, d, i00 = jtheta(t)
    print("tau =", mp.nstr(t, 8), " j_theta =", mp.nstr(j, 15), " |jDen| =", mp.nstr(abs(den), 6))
