"""n = 21: chi_{7,3} versus P_1(7)."""
import sys; sys.path.insert(0, '.')
from heeg import *
I = pari('I')
n, d0 = 21, 7
S, nreps, h, ch = sums_for(n, [1, -1, -7, -3], -8, -64 * n)
print("n=21 classes found", nreps, "h(-64n)=", h, "rep checks", ch)
dl = delta7(d0)
R, nr7, h7, _ = sums_for(d0, [1], dl, -d0)
P7 = R[1]
print("d0=7 delta", dl, "classes", nr7, "h", h7, "P_1(7) on lattice?", in_lattice(4 * P7))
for s in (1, -1):
    i0 = s * I
    van_psi = in_lattice(4 * (S[-1] - i0 * S[1]))
    van_m3 = in_lattice(4 * (S[-3] - i0 * S[-7]))
    print("i0 = %+di: P_psi torsion %s, P_{chi_-3} torsion %s" % (s, van_psi, van_m3))
    z16 = 4 * S[-7] - 4 * i0 * S[-3]          # = 16 P_{chi_{7,3}}
    z16_1 = 4 * S[1] - 4 * i0 * S[-1]         # = 16 P_1(21)
    print("   16 P_chi torsion?", in_lattice(z16), " 16 P_1(21) torsion?", in_lattice(z16_1))
    hits = [m for m in range(-3000, 3001) if in_lattice(z16 - m * P7, 1e-20)]
    print("   m with 16 P_{chi_{7,3}} = m P_1(7):", hits, " -> r =", [m / 16 for m in hits])
