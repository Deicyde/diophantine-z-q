"""dim Sel_2(C_n) - 2 is odd exactly for n = 5, 6, 7 (mod 8): check for all squarefree 1 <= n < N
(sel2cong from rv-route-k).  This is the 2-Selmer parity of Monsky / Birch-Stephens root numbers."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'rv-route-k'))
from sel2cong import selmer
import cypari2
pari = cypari2.Pari()
N = int(sys.argv[1]); bad = 0; cnt = {}
for n in range(1, N):
    if not pari.issquarefree(n):
        continue
    odd = [int(p) for p in pari.factor(n)[0] if int(p) != 2] if n > 1 else []
    s = len(selmer(n, odd)[0]) - 2
    cnt[(n % 8, s)] = cnt.get((n % 8, s), 0) + 1
    if (s % 2 == 1) != (n % 8 in (5, 6, 7)):
        bad += 1
print("violations", bad)
print(sorted(cnt.items()))
