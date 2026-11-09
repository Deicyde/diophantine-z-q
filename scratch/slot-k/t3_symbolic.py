"""Symbolic test of the Theorem of slot-k §2.5 over random abstract data (beta, theta) satisfying only
(theta1)-(theta4), with the Selmer system of descent-alt Proposition 0 (symsel.py).
Usage: t3_symbolic.py TRIALS SEED MAXP MAXT"""
import sys, os, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "descent-alt"))
import symsel

WRONGX = int(os.environ.get("WRONGX", "0"))

def lam(c): return 1 if c % 4 == 3 else 0
def mu(c): return 1 if c % 8 in (3, 5) else 0

def cfg_of(classes, up):
    """classes: list mod 8; up[i][j] (i != j) = [p_j/p_i] for the chosen orientation, with
    reciprocity enforced by the caller.  Returns symsel config."""
    k = len(classes); d = 1
    for c in classes: d = d * c % 8
    return (d, [lam(c) for c in classes], [mu(c) for c in classes], [row[:] for row in up])

def trial(rng, maxp, maxt):
    kP = rng.randint(1, maxp); kT = rng.randint(0, maxt)
    while True:
        cP = [rng.choice((1, 3, 5, 7)) for _ in range(kP)]
        pr = 1
        for c in cP: pr = pr * c % 8
        if pr == 7: break
    while True:
        cT = [rng.choice((1, 3, 5, 7)) for _ in range(kT)]
        pr = 1
        for c in cT: pr = pr * c % 8
        if pr == 1: break
    s = rng.randint(0, 1)
    I = cP + cT; k = len(I)
    L = [[0] * k for _ in range(k)]
    def setsym(i, j, b):   # [I_j / I_i] = b, and the reverse by reciprocity
        L[i][j] = b; L[j][i] = b ^ (lam(I[i]) & lam(I[j]))
    for i in range(k):
        for j in range(i + 1, k):
            setsym(i, j, rng.randint(0, 1))
    # X[p][l] = [p/l] = L[l][p]; impose column sums s*lam_l and row sums 0 (theta3, theta4)
    if kT:
        for li in range(kT):
            l = kP + li
            for pi in range(kP - 1):
                pass
        # fix: last P row adjusts columns; last T column adjusts rows (consistent by total parity)
        for li in range(kT):
            l = kP + li
            col = sum(L[l][p] for p in range(kP)) % 2
            if col != (s & lam(I[l])):
                setsym(l, kP - 1, L[l][kP - 1] ^ 1)
        lT = kP + kT - 1
        for p in range(kP):
            row = sum(L[kP + li][p] for li in range(kT)) % 2
            if row != 0:
                setsym(lT, p, L[lT][p] ^ 1)
        # the last fix may break column lT only if parity fails; check
        for li in range(kT):
            l = kP + li
            assert sum(L[l][p] for p in range(kP)) % 2 == (s & lam(I[l]))
        for p in range(kP):
            assert sum(L[kP + li][p] for li in range(kT)) % 2 == 0
    # slots
    x = (s + 1 + WRONGX) % 2
    names = list(range(k))
    classes = I[:]
    def add(cl, sym_to):     # sym_to: dict index -> [new/idx]
        idx = len(classes); classes.append(cl)
        for row in L: row.append(0)
        L.append([0] * (idx + 1))
        for j in range(idx):
            b = sym_to.get(j, 0)
            L[j][idx] = b                         # [new / I_j]
            L[idx][j] = b ^ (lam(cl) & lam(classes[j]))   # [I_j / new]
        return idx
    p0 = 0; Prest = list(range(1, kP))
    sym = {p: (1 + lam(I[p]) * x) % 2 for p in Prest}
    sym[p0] = (x + sum(sym.values())) % 2
    q0 = add(3, sym)
    RP = [add(1, {p: 1, p0: 1}) for p in Prest]
    RT = [add(1, {l: 1, q0: 1}) for l in range(kP, kP + kT)]
    S1 = list(range(kP)) + [q0] + RP + RT
    S2 = S1 + list(range(kP, kP + kT))
    def sub(S):
        return cfg_of([classes[i] for i in S], [[L[i][j] if i != j else 0 for j in S] for i in S])
    res = []
    for S in (S1, S2):
        C = sub(S)
        dim = symsel.selmer_dim(C)
        res.append((dim, symsel.has_first(C, (1 << kP) - 1, a0=s)))
    return res, kP, kT

if __name__ == "__main__":
    N, seed, maxp, maxt = map(int, sys.argv[1:5])
    rng = random.Random(seed); bad = 0
    for t in range(N):
        res, kP, kT = trial(rng, maxp, maxt)
        if res != [(3, True), (3, True)]:
            bad += 1; print("FAIL", kP, kT, res)
    print(f"trials={N} failures={bad} (omega(beta)<= {maxp}, omega(theta)<= {maxt})")
