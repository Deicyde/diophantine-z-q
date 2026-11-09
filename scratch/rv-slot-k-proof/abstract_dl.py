"""The theorem of slot-k §2.5 on abstract data satisfying only (θ1)–(θ4) and reciprocity.

Own implementation (system.py), independent of scratch/slot-k. Modes:
  exhaustive  all data with |P| <= a, |T| <= b (classes, symbols, sign)
  random      random data with larger |P|, |T|
Variants (env-free, function arguments): xchoice 'good' (x = s+1) or 'bad' (x = s);
q0T 'zero' (prescribed [q0/l] = 0) or 'random' (that condition dropped).
"""
import itertools
import random
import sys
from system import solve, first_coord_in, lam, check_reciprocity

CLS = [1, 3, 5, 7]


def build(cP, cT, s, symP, symT, M, xchoice='good', q0T=None, rng=None):
    """Return the two configurations (classes, symbol matrices) and the index sets.

    cP, cT: classes; symP[(i,j)] for i<j is [P_j/P_i]; symT likewise; M[i][k] = [T_k/P_i].
    """
    nP, nT = len(cP), len(cT)
    x = (s + 1) % 2 if xchoice == 'good' else s
    # index layout: P (0..nP-1), q0, R_P (nP-1 of them, for P[1..]), R_T (nT), T (nT)
    iq = nP
    iRP = list(range(nP + 1, nP + 1 + nP - 1))
    iRT = list(range(nP + nP, nP + nP + nT))
    iT = list(range(nP + nP + nT, nP + nP + 2 * nT))
    N = nP + nP + 2 * nT
    c = list(cP) + [3] + [1] * (nP - 1) + [1] * nT + list(cT)
    S = [[None] * N for _ in range(N)]  # S[a][b] = [b/a]

    def setsym(a, b, val):  # [b/a] = val, and the reverse by reciprocity
        S[a][b] = val
        S[b][a] = val ^ (lam(c[a]) * lam(c[b]))

    for (i, j), v in symP.items():
        setsym(i, j, v)
    for (i, j), v in symT.items():
        setsym(iT[i], iT[j], v)
    for i in range(nP):
        for k in range(nT):
            setsym(i, iT[k], M[i][k])  # [T_k / P_i]
    # q0: [q0/p] prescribed
    qp = {}
    tot = 0
    for i in range(1, nP):
        qp[i] = (1 + lam(cP[i]) * x) % 2
        tot ^= qp[i]
    qp[0] = x ^ tot
    for i in range(nP):
        S[i][iq] = qp[i]  # [q0 / p]
        S[iq][i] = qp[i] ^ (lam(cP[i]) * 1)
    for k in range(nT):
        v = 0 if q0T == 'zero' or q0T is None else rng.randint(0, 1)
        S[iT[k]][iq] = v  # [q0 / l]
        S[iq][iT[k]] = v ^ lam(cT[k])
    # r_p for p = P[i], i >= 1
    for t, i in enumerate(range(1, nP)):
        r = iRP[t]
        for y in range(N):
            if y != r:
                setsym(y, r, 0)
        setsym(i, r, 1)
        setsym(0, r, 1)
    # r_l
    for k in range(nT):
        r = iRT[k]
        for y in range(N):
            if y != r:
                setsym(y, r, 0)
        setsym(iT[k], r, 1)
        setsym(iq, r, 1)
    # the slots' own definitions above overwrite only slot rows; re-impose r_p rows after r_l
    for t, i in enumerate(range(1, nP)):
        r = iRP[t]
        for y in range(N):
            if y != r and y not in iRT:
                setsym(y, r, 0)
        setsym(i, r, 1)
        setsym(0, r, 1)
    for a in range(N):
        S[a][a] = 0
    assert all(S[a][b] is not None for a in range(N) for b in range(N))
    assert check_reciprocity(c, S)
    # first curve: drop T
    keep1 = [a for a in range(N) if a not in iT]
    c1 = [c[a] for a in keep1]
    S1 = [[S[a][b] for b in keep1] for a in keep1]
    uP1 = [keep1.index(i) for i in range(nP)]
    return (c1, S1, uP1), (c, S, list(range(nP)))


def check(cP, cT, s, symP, symT, M, **kw):
    (c1, S1, u1), (c2, S2, u2) = build(cP, cT, s, symP, symT, M, **kw)
    out = []
    for c, S, uset in [(c1, S1, u1), (c2, S2, u2)]:
        sols = solve(c, S)
        out.append((len(sols), first_coord_in(sols, len(c), s, uset)))
    return out


def all_data(nP, nT):
    for cP in itertools.product(CLS, repeat=nP):
        p = 1
        for t in cP:
            p = p * t % 8
        if p != 7:
            continue
        for cT in itertools.product(CLS, repeat=nT):
            q = 1
            for t in cT:
                q = q * t % 8
            if q != 1:
                continue
            pairsP = [(i, j) for i in range(nP) for j in range(i + 1, nP)]
            pairsT = [(i, j) for i in range(nT) for j in range(i + 1, nT)]
            for s in range(2):
                for bP in itertools.product(range(2), repeat=len(pairsP)):
                    for bT in itertools.product(range(2), repeat=len(pairsT)):
                        for M in matrices(cP, cT, s):
                            yield cP, cT, s, dict(zip(pairsP, bP)), dict(zip(pairsT, bT)), M


def matrices(cP, cT, s):
    """All M with row sums 0 ((θ4)) and column sums (s+1)λ_l ((θ3) with reciprocity)."""
    nP, nT = len(cP), len(cT)
    if nT == 0:
        yield [[] for _ in range(nP)]
        return
    free = (nP - 1) * (nT - 1)
    for bits in itertools.product(range(2), repeat=free):
        yield complete(cP, cT, s, bits)


def complete(cP, cT, s, bits):
    nP, nT = len(cP), len(cT)
    M = [[0] * nT for _ in range(nP)]
    it = iter(bits)
    for i in range(nP - 1):
        for k in range(nT - 1):
            M[i][k] = next(it)
    for i in range(nP - 1):
        M[i][nT - 1] = sum(M[i][:nT - 1]) % 2
    for k in range(nT):
        col = ((s + 1) * lam(cT[k])) % 2
        M[nP - 1][k] = (col + sum(M[i][k] for i in range(nP - 1))) % 2
    assert sum(M[nP - 1]) % 2 == 0
    # check (θ3), (θ4) directly from the definitions
    for i in range(nP):
        assert sum(M[i]) % 2 == 0  # [θ/p] = 0
    for k in range(nT):
        beta_l = (s * lam(cT[k]) + sum(M[i][k] ^ (lam(cP[i]) * lam(cT[k])) for i in range(nP))) % 2
        assert beta_l == 0  # [β/l] = 0
    return M


def random_data(rng, nP, nT):
    while True:
        cP = [rng.choice(CLS) for _ in range(nP)]
        p = 1
        for t in cP:
            p = p * t % 8
        if p == 7:
            break
    while True:
        cT = [rng.choice(CLS) for _ in range(nT)]
        q = 1
        for t in cT:
            q = q * t % 8
        if q == 1:
            break
    s = rng.randint(0, 1)
    symP = {(i, j): rng.randint(0, 1) for i in range(nP) for j in range(i + 1, nP)}
    symT = {(i, j): rng.randint(0, 1) for i in range(nT) for j in range(i + 1, nT)}
    M = complete(cP, cT, s, [rng.randint(0, 1) for _ in range(max(0, (nP - 1) * (nT - 1)))]) \
        if nT else [[] for _ in range(nP)]
    return cP, cT, s, symP, symT, M


if __name__ == "__main__":
    mode = sys.argv[1]
    variant = dict(xchoice=sys.argv[2] if len(sys.argv) > 2 else 'good',
                   q0T=sys.argv[3] if len(sys.argv) > 3 else 'zero')
    rng = random.Random(7)
    variant['rng'] = rng
    tally = {}
    if mode == 'exhaustive':
        sizes = [(a, b) for a in range(1, 4) for b in range(0, 4) if a + b <= int(__import__("os").environ.get("MAXSUM", "5"))]
        for nP, nT in sizes:
            n = bad = 0
            for data in all_data(nP, nT):
                r = check(*data, **variant)
                n += 1
                if r != [(3, True), (3, True)]:
                    bad += 1
                    tally[str(r)] = tally.get(str(r), 0) + 1
            print("exhaustive |P|=%d |T|=%d: %d cases, %d failures" % (nP, nT, n, bad), flush=True)
    else:
        trials = int(sys.argv[4]) if len(sys.argv) > 4 else 300
        maxP, maxT = 10, 10
        n = bad = 0
        badT3 = 0
        for t in range(trials):
            nP, nT = rng.randint(1, maxP), rng.randint(0, maxT)
            data = random_data(rng, nP, nT)
            r = check(*data, **variant)
            n += 1
            if r != [(3, True), (3, True)]:
                bad += 1
                tally[str(r)] = tally.get(str(r), 0) + 1
                if any(lam(cl) for cl in data[1]):
                    badT3 += 1
        print("random: %d cases, %d failures (%d with a prime ≡ 3 mod 4 in θ)" % (n, bad, badT3))
    print("failure types:", tally)
