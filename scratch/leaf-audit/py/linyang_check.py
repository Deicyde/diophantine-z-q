# leaf-audit: numerical check of the corrected (existential) LinYangEx29 with j6 := j_theta (QMHauptmodul's f),
# through Igusa's theta expressions: s2 = psi4Th, s3 = psi6Th, s5 = 2^12 3^5 chi10Th, s6 = 2^12 3^6 chi12Th, all parsed
# from ZInQKernel/Contrib/OneProof/LinYangGlue.lean (psi6Th, chi12Th) and LPrefix (thetaSum8, thetaProd2).
# Checks s3^2 = j s2^3, s5 = s2 s3, s6 = (j+1) s2^3 at a few tau, with j = jNum/jDen(Omega tau).
import re, sys
sys.path.insert(0, sys.argv[1])
import mpmath as mp
from jtheta_nonreal import Omega, theta, chars, s2 as SQ2
mp.mp.dps = 40
src = open(sys.argv[2]).read()
def parse(name):
    body = src[src.index("def %s" % name):]
    body = body[:body.index("\n\n")]
    lines = body.split("\n")[1:]
    terms = []
    for ln in lines:
        cs = re.findall(r"thetaConst \(!\[(\d), (\d)\], !\[(\d), (\d)\]\)", ln)
        if not cs: continue
        st = ln.strip()
        sign = -1 if st.startswith("-") else 1
        terms.append((sign, [((int(a), int(b)), (int(c), int(d))) for a, b, c, d in cs]))
    return terms
P6 = parse("psi6Th"); C12 = parse("chi12Th")
print("psi6Th terms:", len(P6), " chi12Th terms:", len(C12))
def ev(terms, th):
    return sum(s * mp.fprod([th[m] for m in ms])**4 for s, ms in terms)
for t in [mp.mpc(0.3, 1.1), mp.mpc(0.1, 0.9), mp.mpc(-0.4, 1.3), SQ2 + 1j]:
    Om = Omega(t)
    th = {m: theta(m, Om) for m in chars}
    S8 = sum(x**8 for x in th.values()); P2 = mp.fprod([x**2 for x in th.values()])
    j = 3779136 * P2**2 / S8**5
    s2v = S8/4; s3v = ev(P6, th)/4
    s5v = 2**12 * 3**5 * (-P2 / 2**14); s6v = 2**12 * 3**6 * ev(C12, th) / (2**17 * 3)
    r1 = abs(s3v**2 - j*s2v**3)/abs(s3v**2); r2 = abs(s5v - s2v*s3v)/abs(s5v) if abs(s5v) > 0 else abs(s2v*s3v)
    r3 = abs(s6v - (j+1)*s2v**3)/abs(s6v)
    print("tau =", mp.nstr(t, 8), " j =", mp.nstr(j, 12), " rel.err s3^2=j s2^3:", mp.nstr(r1, 3),
          " s5=s2 s3:", mp.nstr(r2, 3), " s6=(j+1)s2^3:", mp.nstr(r3, 3))
