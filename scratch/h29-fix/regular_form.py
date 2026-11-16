"""h29-fix: n = x^2 + y^2 + 16 z^2 (TYZ L531-533, Jones-Pall Thm 5 as cited). Exhaustive check up to N."""
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
two = bytearray(N + 1)
x = 0
while x * x <= N:
    y = x
    while x * x + y * y <= N:
        two[x * x + y * y] = 1
        y += 1
    x += 1
rep = bytearray(N + 1)
z = 0
while 16 * z * z <= N:
    s = 16 * z * z
    for m in range(0, N + 1 - s):
        if two[m]:
            rep[m + s] = 1
    z += 1
bad1 = [n for n in range(1, N + 1, 8) if not rep[n]]
print("N =", N, "; n = 1 (mod 8) not represented:", bad1[:10], len(bad1))
non = [n for n in range(1, 400) if not rep[n]]
print("non-represented n < 400:", non)
# classes of non-represented n (odd part / 2-adic): residues mod 64
from collections import Counter
print("non-represented n < 20000 by residue mod 32:", sorted(Counter(n % 32 for n in range(1, 20000) if not rep[n]).items()))

def excluded(n):
    if n % 4 == 3 or n % 8 == 6 or n % 16 == 12:
        return True
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7
mism = [n for n in range(1, N + 1) if bool(rep[n]) == excluded(n)]
print("characterization [not rep <=> n = 3 (4), 6 (8), 12 (16) or 4^a(8k+7)] mismatches up to N:", mism[:10], len(mism))
