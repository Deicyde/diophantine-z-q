"""cr3-trust: select inputs for the TYZClRk check (selection only, not ground truth).
For squarefree d = 5 mod 8, 3..5 primes, d < 30000: T5b(d) from Redei bits (Lean T5b; Lean proves
T5bCl = T5b, RouteK.Redei.T5bCl_eq_T5b') and #Sel2(C_d) from rv-cr5b-sec3/mirror.py (local images).
Lists the d with T5b = 1 and #Sel2 > 8, and counts the rest."""
import sys
sys.path.insert(0, "scratch/rv-cr5b-sec3")
import mirror as m

big, eight, tot = [], 0, 0
for d in range(5, 30000, 8):
    if not m.pari.issquarefree(d):
        continue
    b = m.Bits(d)
    if not 3 <= b.r <= 5:
        continue
    t, _ = m.T5b(b)
    if t != 1:
        continue
    tot += 1
    s = len(m.sel2(d))
    if s > 8:
        big.append((d, b.P, s))
    else:
        eight += 1
print("T5b=1 count:", tot, " with #Sel2=8:", eight, " with #Sel2>8:", len(big))
for x in big:
    print(x)
