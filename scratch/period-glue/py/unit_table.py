"""period-glue: UnitLiftMod3 certificate. For each class c in (Z/3)^4 (coordinates in N5's basis of O)
with nrd(c) != 0 mod 3, find a unit of O (nrdZ = +-1) congruent to c mod 3.
nrdZ(n) = n0^2 + n0 n2 + n2^2 - 2 n1^2 - 2 n1 n3 - 2 n3^2 (reduced norm of ofInt n).
Run: ~/pyenv/bin/python -I unit_table.py"""
import itertools
def nrdZ(n): n0,n1,n2,n3 = n; return n0*n0 + n0*n2 + n2*n2 - 2*n1*n1 - 2*n1*n3 - 2*n3*n3
table = {}
for B in range(1, 12):
    for n in itertools.product(range(-B, B+1), repeat=4):
        if nrdZ(n) in (1, -1):
            c = tuple(x % 3 for x in n)
            if c not in table: table[c] = n
    inv = [c for c in itertools.product(range(3), repeat=4) if nrdZ(c) % 3 != 0]
    if all(c in table for c in inv): break
inv = [c for c in itertools.product(range(3), repeat=4) if nrdZ(c) % 3 != 0]
print("invertible classes:", len(inv), " covered:", sum(c in table for c in inv), " box:", B)
print("max |coord|:", max(max(abs(x) for x in table[c]) for c in inv))
# Lean vector indexed by enc(c) = c0 + 3 c1 + 9 c2 + 27 c3 (entries for non-invertible classes: ![1,0,0,0])
entries = []
for idx in range(81):
    c = (idx % 3, (idx // 3) % 3, (idx // 9) % 3, (idx // 27) % 3)
    n = table.get(c, (1,0,0,0)) if c in inv else (1,0,0,0)
    entries.append("![%d, %d, %d, %d]" % n)
print("LEAN_TABLE ![" + ", ".join(entries) + "]")
