"""Find Mordell curves y^2 = x^3 + k (k supported on 2,3,5, sixth-power free) whose traces match
the two elliptic factors of the Jacobian of y^2 = F(u) (traces from curve.py, part (d))."""
def leg(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)
def ap(k, p):
    return -sum(leg(x**3 + k, p) for x in range(p))
# factor traces from curve.py: at p = 7,19,31,43 the two factors have traces +-a; at 13, 37 equal
fac = {7: 4, 13: -2, 19: 8, 31: 4, 37: -10, 43: 8}
hits = []
for a in range(6):
    for b in range(6):
        for c in range(6):
            for s in (1, -1):
                k = s * 2**a * 3**b * 5**c
                tr = {p: ap(k, p) for p in fac}
                if all(abs(tr[p]) == abs(fac[p]) for p in fac) and tr[13] == -2 and tr[37] == -10:
                    hits.append((k, tr))
for k, tr in hits[:12]:
    print(k, tr)
print(len(hits), "matches")
