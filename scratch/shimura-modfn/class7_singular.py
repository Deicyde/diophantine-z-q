# Class-7 TYZ points (n ≡ 7 mod 8 squarefree, D = -n): the Heegner point of tyzForm7 n is a
# non-isolated point of the plane model (j, j_32) iff [p2]^10 = 1 in Cl(K_n) (the only O-stable
# cyclic 32-isogenies of L are p2^-5 L and p2bar^-5 L), i.e. iff p2^10 = (alpha) with
# alpha = (a + b sqrt(-n))/2, a ≡ b (mod 2), N(alpha) = (a^2 + n b^2)/4 = 2^10, alpha/2 not integral.
# This forces b != 0 and n <= 4096: a finite list.  Usage: python3 -I class7_singular.py
def sqf(n): return all(n % (p * p) for p in range(2, int(n ** 0.5) + 1))
out = []
for n in range(7, 4097, 8):
    if not sqf(n): continue
    ok = False
    for b in range(1, 65):
        r = 4096 - n * b * b
        if r < 0: break
        a = int(round(r ** 0.5))
        if a * a != r or (a - b) % 2: continue
        # alpha/2 = (a + b sqrt(-n))/4 integral iff a ≡ b (mod 4)?  (a/2 + b/2 sqrt(-n))/2 in O_K
        # iff a/2 ≡ b/2 (mod 2) with a, b even.
        if a % 2 == 0 and b % 2 == 0 and ((a // 2) - (b // 2)) % 2 == 0: continue
        ok = True; break
    if ok: out.append(n)
print('n ≡ 7 (mod 8) squarefree with [p2]^10 = 1 (non-isolated tyzForm7):', out)
