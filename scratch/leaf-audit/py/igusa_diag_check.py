# leaf-audit: independent check of the theta side of IgusaThetaExpressions on the diagonal Omega = diag(t1, t2):
# psi4Th -> E4(t1)E4(t2), psi6Th -> E6(t1)E6(t2), chi10Th -> 0, chi12Th -> Delta(t1)Delta(t2) (the restrictions of
# Igusa's psi4, psi6, chi10, chi12; for k = 4, 6 the Eisenstein series restrict to E_k (x) E_k since S_k(SL2(Z)) = 0).
# psi6Th, chi12Th parsed from LinYangGlue.lean; thetaConst as in LPrefix.lean.
import re, sys
import mpmath as mp
mp.mp.dps = 30
src = open(sys.argv[1]).read()
def parse(name):
    body = src[src.index("def %s" % name):]
    body = body[:body.index("\n\n")]
    terms = []
    for ln in body.split("\n")[1:]:
        cs = re.findall(r"thetaConst \(!\[(\d), (\d)\], !\[(\d), (\d)\]\)", ln)
        if cs:
            terms.append((-1 if ln.strip().startswith("-") else 1,
                          [((int(a), int(b)), (int(c), int(d))) for a, b, c, d in cs]))
    return terms
P6, C12 = parse("psi6Th"), parse("chi12Th")
def theta(m, Om, R=10):
    (a0, a1), (b0, b1) = m; tot = mp.mpc(0)
    for n0 in range(-R, R+1):
        for n1 in range(-R, R+1):
            v = [n0 + mp.mpf(a0)/2, n1 + mp.mpf(a1)/2]
            q = sum(v[i]*Om[i][j]*v[j] for i in range(2) for j in range(2))
            tot += mp.exp(mp.pi*1j*q + mp.pi*1j*(v[0]*b0 + v[1]*b1))
    return tot
chars = [((a0,a1),(b0,b1)) for a0 in (0,1) for a1 in (0,1) for b0 in (0,1) for b1 in (0,1) if (a0*b0+a1*b1) % 2 == 0]
def sigma(n, k): return sum(d**k for d in range(1, n+1) if n % d == 0)
def E(k, t, N=60):
    q = mp.exp(2j*mp.pi*t); c = {4: 240, 6: -504}[k]
    return 1 + c*sum(sigma(n, k-1)*q**n for n in range(1, N))
def Delta(t, N=60):
    q = mp.exp(2j*mp.pi*t); return q*mp.fprod([(1-q**n)**24 for n in range(1, N)])
def ev(terms, th): return sum(s*mp.fprod([th[m] for m in ms])**4 for s, ms in terms)
for (t1, t2) in [(mp.mpc(0.1, 1.2), mp.mpc(-0.3, 0.9)), (mp.mpc(0.25, 1.0), mp.mpc(0.4, 1.5))]:
    Om = [[t1, 0], [0, t2]]
    th = {m: theta(m, Om) for m in chars}
    p4 = sum(x**8 for x in th.values())/4; p6 = ev(P6, th)/4
    c10 = -mp.fprod([x**2 for x in th.values()])/2**14; c12 = ev(C12, th)/(2**17*3)
    print("t1,t2 =", mp.nstr(t1,4), mp.nstr(t2,4),
          " |psi4Th/E4E4-1| =", mp.nstr(abs(p4/(E(4,t1)*E(4,t2))-1), 3),
          " |psi6Th/E6E6-1| =", mp.nstr(abs(p6/(E(6,t1)*E(6,t2))-1), 3),
          " |chi10Th| =", mp.nstr(abs(c10), 3),
          " |chi12Th/(Delta Delta)-1| =", mp.nstr(abs(c12/(Delta(t1)*Delta(t2))-1), 3))
