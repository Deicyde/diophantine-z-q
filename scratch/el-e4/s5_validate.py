# Validate the criterion  C_m(Q) != empty <=> core(-m R) in span(alpha(T)=core(ac), alpha(gens))
# on random small instances (m, Th, R): compare with hyperellratpoints (height 10^4).
import sys, random; sys.path.insert(0, "scratch/el-e4")
from fractions import Fraction as Fr
import cypari2; pari = cypari2.Pari(); pari.allocatemem(2*10**9)
src = open("scratch/el-e4/s5_global.py").read()
exec(src[src.index("def core"):src.index("random.seed(2026)")])
from locsol import quartic
random.seed(3); stats = {}
for _ in range(150):
    m = random.choice([1, -1, 2, -2, 3, -3, 5, 6, -7]); R = random.choice([2, 3, 5, 6, 7, 10, 11, 13, 14, 15])
    Th = Fr(random.randint(1, 30), random.randint(1, 12))
    f = quartic(m, Th, R); L = Th.denominator
    fi = [int(c * L * L) for c in f]
    pts = pari.hyperellratpoints(pari.Pol(list(reversed(fi))), 10**4)
    b = 2*m*R*R; ac = -m*m*R**3*(m*Th*Th - R)
    E = pari.ellinit([0, str(b), 0, str(ac), 0]); rk = pari.ellrank(E); g = rk[3]
    if len(g): g = pari.ellsaturation(E, g, 2)
    al = [core(ac)] + [core(P[0]) for P in g if P[0] != 0]
    d = core(-m*R); hit = d == 1 or span_has(al, d)
    key = (bool(len(pts)), hit, int(rk[0]) == int(rk[1])); stats[key] = stats.get(key, 0) + 1
print("(points found, criterion hit, rank decided): count")
for k, v in sorted(stats.items()): print(k, v)
