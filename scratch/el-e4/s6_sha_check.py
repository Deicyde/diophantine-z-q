# Step 6: independent check that a locally soluble, non-hit C_m is a nontrivial Sha element.
# (a) ellrank on the Jacobian E_J itself: [r, R, s, pts] (s = 2-rank of Sha(E_J)[2] lower bound per PARI doc
#     when available); (b) p-adic points by brute force: for each prime p in a bad set, find q mod p^6 with
#     f(q) a nonzero square class witnessed to precision (independent of locsol's recursion).
import sys, json; sys.path.insert(0, "scratch/el-e4")
from fractions import Fraction as Fr
import cypari2; pari = cypari2.Pari(); pari.allocatemem(2*10**9)
import k0; from locsol import quartic
src = open("scratch/el-e4/s5_global.py").read(); exec(src[src.index("def core"):src.index("def span_has")])
R = json.load(open("scratch/el-e4/s5_out.json"))
def brute_local(f, p, K=7):
    # search q = x/p^j (j=0..2) with x mod p^K s.t. f(q) has even valuation e < K-3 and unit part square (mod p or mod 8)
    for j in range(0, 3):
        for x in range(p ** min(K, 5)):
            q = Fr(x, p ** j); val = sum(c * q ** i for i, c in enumerate(f))
            if val == 0: return True
            nu, de = val.numerator, val.denominator; v = 0
            while nu % p == 0: nu //= p; v += 1
            while de % p == 0: de //= p; v -= 1
            if v % 2: continue
            u = (nu * pow(de, -1, p ** 3)) % p ** 3
            if (p == 2 and u % 8 == 1) or (p > 2 and pow(u, (p - 1) // 2, p) == 1):
                # stability: perturb q by p^(K) changes f by >= p^(K - 4j) ; require margin
                return True
    return False
done = 0
for r in R:
    for c in r["curves"]:
        if c["inAlphaImage"] or not c["decided"] or done >= 6: continue
        m = c["m"]; R1 = r["R1"]; Th0 = Fr(r["Th0"]); s = int(pari.sqrtint(int(k0.testR0(1, Fr(r["n"])) / R1)))
        Th = Th0 / s; f = quartic(m, Th, R1)
        a, b, cc = f[4], f[2], f[0]
        EJ = pari.ellinit([0, str(-2*b), 0, str(b*b - 4*a*cc), 0]); rkJ = pari.ellrank(EJ)
        D = Fr(str(pari.ellinit([0, str(b), 0, str(a*cc), 0])[11]))
        bad = sorted(set(int(p) for p in pari.factor(abs(D.numerator * D.denominator) * 2 * abs(m) * R1)[0] if int(p) < 200))
        loc = {p: brute_local(f, p) for p in bad}
        print(f"n={r['n']} Th0={r['Th0']} m={m}: rank E = {c['rank_lo']}; ellrank(E_J) = [{rkJ[0]}, {rkJ[1]}, {rkJ[2]}]; brute local at {bad}: {all(loc.values())}", flush=True)
        done += 1
