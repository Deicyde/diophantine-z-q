"""Table for `exists_unit_congr`: for each c in (Z/3)^4 (index c0+3c1+9c2+27c3) with
nrd(c) != 0 mod 3, a unit n of O (nrdC n = +-1) with n = c mod 3; else (0,0,0,0)."""
from itertools import product
def nrdC(n): return n[0]**2 + n[0]*n[2] + n[2]**2 - 2*(n[1]**2 + n[1]*n[3] + n[3]**2)
units = sorted((n for n in product(range(-4, 5), repeat=4) if abs(nrdC(n)) == 1),
               key=lambda n: sum(abs(x) for x in n))
tbl = []
for k in range(81):
    c = (k % 3, (k // 3) % 3, (k // 9) % 3, (k // 27) % 3)
    if nrdC(c) % 3 == 0:
        tbl.append((0, 0, 0, 0)); continue
    n = next(n for n in units if all((n[i] - c[i]) % 3 == 0 for i in range(4)))
    tbl.append(n)
print("units found for", sum(1 for k in range(81) if tbl[k] != (0,0,0,0)), "residues")
lean = "def unitTbl : List (Fin 4 → ℤ) :=\n  [" + ",\n   ".join("![%d, %d, %d, %d]" % n for n in tbl) + "]\n"
open('units_table.lean.part', 'w').write(lean)
