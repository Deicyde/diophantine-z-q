# Step 7: undecided rank-(1,1) curves of s5 whose generator was not found: retry ellrank with higher effort
# (cap per curve via alarm), then decide hit/non-hit.  Input: s5_out.json.  Sample: first N such curves.
import sys, json, time, signal; sys.path.insert(0, "scratch/el-e4")
from fractions import Fraction as Fr
import cypari2; pari = cypari2.Pari(); pari.allocatemem(4*10**9)
import k0; from locsol import quartic
src = open("scratch/el-e4/s5_global.py").read(); exec(src[src.index("def core"):src.index("random.seed(2026)")])
N = int(sys.argv[1]); EFF = int(sys.argv[2]); TL = int(sys.argv[3])
R = json.load(open("scratch/el-e4/s5_out.json")); cnt = 0; tally = {}
class TO(Exception): pass
def h(*a): raise TO()
signal.signal(signal.SIGALRM, h)
for r in R:
    for c in r["curves"]:
        if c["decided"] or (c["rank_lo"], c["rank_hi"]) != (1, 1) or cnt >= N: continue
        cnt += 1; m = c["m"]; R1 = r["R1"]; s = int(pari.sqrtint(int(k0.testR0(1, Fr(r["n"])) / R1)))
        Th = Fr(r["Th0"]) / s; b = 2*m*R1*R1; ac = -m*m*R1**3*(m*Th*Th - R1)
        E = pari.ellinit([0, str(b), 0, str(ac), 0]); t0 = time.time()
        signal.alarm(TL)
        try:
            rk = pari.ellrank(E, EFF); pts = rk[3]; signal.alarm(0)
        except (TO, cypari2.PariError) as e:
            signal.alarm(0); print(f"n={r['n']} m={m}: timeout/err", flush=True); tally["timeout"] = tally.get("timeout", 0) + 1; continue
        if len(pts) < 1: res = "no gen"
        else:
            pts = pari.ellsaturation(E, pts, 2)
            al = [core(ac)] + [core(P[0]) for P in pts if P[0] != 0]
            res = "HIT" if span_has(al, core(-m*R1)) else "not hit"
            if res == "HIT": res += f" (gen height {float(pari.ellheight(E, pts[0])):.1f})"
        tally[res.split()[0] + " " + (res.split()[1] if res.startswith("not") else "")] = tally.get(res.split()[0] + " " + (res.split()[1] if res.startswith("not") else ""), 0) + 1
        print(f"n={r['n']} Th0={r['Th0']} m={m}: {res} [{time.time()-t0:.0f}s]", flush=True)
print(tally)
