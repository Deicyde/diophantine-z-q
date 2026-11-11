# Step 3: 30 genuine test-site instances (Lean formulas via k0.py: testC, testR0, Theta0 = 2 Re W0^{-1},
# W0 = prod(1 + R0 C_j^2), M1/E4 so R0 inside W).  n in 1..5, kappa = 1, six shift pairs (h, s0).
# For each: partial factorization of num/den Theta0 (trial division to 1e7), honesty at contact primes,
# obstruction primes  Obs = {p | num Theta0, p not | 2 R0, (R0/p) = -1}, and for each of the 64 signed
# divisors m of 2730 the local solubility of C_m at every determined bad prime (locsol), with Obs
# handled by el-cert's criterion (-m/p) = -1 (re-checked by locsol at p < 1e4).
import sys, time, json; sys.path.insert(0, "scratch/el-e4")
from fractions import Fraction as Fr
import cypari2; pari = cypari2.Pari(); pari.allocatemem(2*10**9)
import k0; from locsol import locsol, quartic
LIM = 10**7
divs = sorted({s*d for d in range(1, 2731) if 2730 % d == 0 for s in (1, -1)})
pairs = [(2, 3), (3, 5), (2, 7), (5, 2), (3, 4), (4, 7)]
out = []
for n in range(1, 6):
    for (h, s0) in pairs:
        t0 = time.time(); t = Fr(n)
        C = k0.testC(n, 1, t, h, s0); R0 = k0.testR0(1, t); Th = k0.theta(R0, C)
        if Th is None or Th == 0: print(n, h, s0, "degenerate"); continue
        N, D = abs(Th.numerator), Th.denominator
        fN = pari.factor(N, LIM); fD = pari.factor(D, LIM); fR = pari.factor(R0.numerator)
        Rp = {int(fR[0][i]): int(fR[1][i]) for i in range(len(fR[0]))}
        def split(fa):
            sm, cof = {}, 1
            for i in range(len(fa[0])):
                p, e = int(fa[0][i]), int(fa[1][i])
                if p < LIM: sm[p] = e
                else: cof *= p ** e
            return sm, cof
        sN, cN = split(fN); sD, cD = split(fD)
        vTh = {p: sN.get(p, 0) - sD.get(p, 0) for p in set(sN) | set(sD)}
        honest = all(2 * vTh.get(p, 0) < e for p, e in Rp.items() if e % 2 == 1)
        obs = [p for p in sN if p > 2 and p not in Rp and pari.kronecker(R0.numerator, p) == -1]
        # contact primes with v_p(R0) odd are skipped: for honest data (2v(Th0) < v(R0)) they are soluble
        # by lemma L1 (q = 0 disc); kappa = 1 data is not honest there (deep multiples are out of reach).
        contact_odd = [p for p, e in Rp.items() if e % 2 == 1 and p > 13]
        bad = sorted((set([2, 3, 5, 7, 11, 13]) | set(Rp) | set(sD) | set(p for p in sN if p not in obs)) - set(contact_odd))
        bad = [p for p in bad if p < 10**6]
        surv = []; fails = {}
        nobs = sum(1 for m in divs if all(pari.kronecker(-m, p) == -1 for p in obs if m % p))
        for m in divs:
            f = quartic(m, Th, R0)
            if not all(pari.kronecker(-m, p) == -1 for p in obs if m % p): continue
            ok = True; failp = None
            for p in sorted(set(bad) | set(q for q in (2, 3, 5, 7, 13) if m % q == 0)):
                r = locsol(f, p, depth=30)
                if r is not True: ok = False; failp = (p, r); break
            if ok: surv.append(m)
            else: fails[str(failp)] = fails.get(str(failp), 0) + 1
        rec = dict(n=n, h=h, s0=s0, digN=len(str(N)), digD=len(str(D)), honest=honest, obs=obs,
                   cofN_digits=len(str(cN)) if cN > 1 else 0, nsurv=len(surv), surv=surv, pass_obs=nobs, fails=fails, contact_odd=contact_odd,
                   sec=round(time.time() - t0, 1))
        out.append(rec); print(json.dumps(rec), flush=True)
json.dump(out, open("scratch/el-e4/s3_out.json", "w"))
