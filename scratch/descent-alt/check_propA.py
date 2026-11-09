"""Checks of Proposition A on actual pole inputs (exact Selmer groups from sel2cong):
 (ii)  beta is a first coordinate of Sel2(C_{beta theta}) iff A v = r_beta has a solution v supported
       on the primes = 1 (mod 4) of beta theta, r_beta = (0, mu_Theta) [beta = 5 (8)] or
       r_beta in {(mu_B, 0), (0, mu_Theta)} [beta = 7 (8)];
 (iii) if every prime of theta is = 1 (mod 4) then (1, theta) lies in Sel2(C_{beta theta})."""
import sys, random
from common import *
import symsel
rng = random.Random(int(sys.argv[1]))
n_ii = n_iii = bad = 0
while n_ii < int(sys.argv[2]):
    B = gen_random(rng, ulim=10 ** 4)
    for m in DIVS:
        beta, theta = beta_theta(B, m)
        beta = abs(beta)
        if beta % 2 == 0 or theta == 1 or beta % 8 not in (5, 7):
            continue
        bp, tp = oddprimes(beta), oddprimes(theta)
        ps = bp + tp; k = len(ps)
        cfg = symsel.config_of(ps)
        _, lam, mu, L = cfg
        A = [[L[i][j] for j in range(k)] for i in range(k)]
        for i in range(k):
            A[i][i] = sum(L[i]) % 2
        P1 = [j for j in range(k) if lam[j] == 0]
        rhs = []
        muB = [mu[i] if i < len(bp) else 0 for i in range(k)]
        muT = [mu[i] if i >= len(bp) else 0 for i in range(k)]
        rhs = [muT] if beta % 8 == 5 else [muB, muT]
        def solvable(r):
            # Gaussian elimination on columns P1
            rows = []
            for i in range(k):
                v = 0
                for c, j in enumerate(P1):
                    if A[i][j]: v |= 1 << c
                rows.append((v, r[i]))
            piv = []
            for v, b in rows:
                for pv, pb, h in piv:
                    if v >> h & 1: v ^= pv; b ^= pb
                if v:
                    piv.append((v, b, v.bit_length() - 1))
                elif b:
                    return False
            return True
        crit = any(solvable(r) for r in rhs)
        basis, gens = sel(beta * theta)
        truth = first_coord_contains(basis, vec_of(beta, gens))
        n_ii += 1
        if crit != truth:
            bad += 1; print("MISMATCH (ii)", B, m)
        if all(p % 4 == 1 for p in tp):
            n_iii += 1
            # (1, theta) in Sel2?  test membership of the pair in the span
            sp = F2Span()
            kk = len(gens)
            for a, b in basis: sp.add(a | (b << kk))
            if sp.reduce(vec_of(1, gens) | (vec_of(theta, gens) << kk)) != 0:
                bad += 1; print("MISMATCH (iii)", B, m)
print(f"(ii) checked on {n_ii} pairs, (iii) on {n_iii} pairs, mismatches {bad}")
