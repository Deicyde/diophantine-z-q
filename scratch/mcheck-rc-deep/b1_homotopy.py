"""mcheck-rc-deep, block 1: the transferred-homotopy identities in "The local diagrams underlying the
coefficient push" (tex L3337-3358, identity at L3354) and the witness transport in paragraph 8 (L3393-3400).

Random model over F_p (p = 10007): four complexes X_0..X_3, each U_k (+) contractible part, conjugated by a
random graded automorphism, with contraction (i_k, p_k, h_k): p i = 1, 1 - i p = d h + h d.
Random chain maps F: X0->X1, G: X1->X2, H: X2->X3 of the form i phi p + d s + s d.
Checks:
  (a) (GF)_L - G_L F_L = d K(G,F) + K(G,F) d with K(G,F) = p G h F i, F_L = p F i;
  (b) K(H,GF) - K(HG,F) + H_L K(G,F) - K(H,G) F_L = L d - d L with L = p H h G h F i  (as printed);
  (c) for a cycle z: p'Fz - p'F i p z = d(p'F h z);  and z - z' = dq => pz - pz' = d(pq).
"""
import random

random.seed(11)
P = 10007


def zeros(r, c):
    return [[0] * c for _ in range(r)]


def mm(A, B):
    n, m, k = len(A), len(B), len(B[0]) if B else 0
    C = zeros(n, k)
    for i in range(n):
        Ai = A[i]
        for t in range(m):
            a = Ai[t]
            if a:
                Bt = B[t]
                Ci = C[i]
                for j in range(k):
                    Ci[j] = (Ci[j] + a * Bt[j]) % P
    return C


def add(A, B, s=1):
    return [[(a + s * b) % P for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def inv(A):
    n = len(A)
    M = [row[:] + e for row, e in zip(A, eye(n))]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c])
        M[c], M[piv] = M[piv], M[c]
        iv = pow(M[c][c], P - 2, P)
        M[c] = [x * iv % P for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]
                M[r] = [(x - f * y) % P for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def iszero(A):
    return all(x == 0 for row in A for x in row)


DEG = range(0, 4)


def make_complex():
    # small model U: dims per degree; contractible pairs (deg j, j+1)
    udeg = [1]  # nonempty small model (avoids empty matrices)
    for j in DEG:
        udeg += [j] * random.randint(0, 2)
    pairs = []
    for j in range(0, 3):
        pairs += [j] * random.randint(0, 2)
    degs = udeg[:]
    a_idx, b_idx = [], []
    for j in pairs:
        a_idx.append(len(degs)); degs.append(j)
        b_idx.append(len(degs)); degs.append(j + 1)
    n, nu = len(degs), len(udeg)
    d = zeros(n, n); h = zeros(n, n)
    for a, b in zip(a_idx, b_idx):
        d[b][a] = 1  # d a = b   (matrices act on column vectors)
        h[a][b] = 1  # h b = a
    i = zeros(n, nu); p = zeros(nu, n)
    for k in range(nu):
        i[k][k] = 1; p[k][k] = 1
    # random graded automorphism S (block-diagonal by degree)
    S = zeros(n, n)
    while True:
        for r in range(n):
            for c in range(n):
                S[r][c] = random.randrange(P) if degs[r] == degs[c] else 0
        try:
            Si = inv(S); break
        except StopIteration:
            continue
    d = mm(mm(S, d), Si); h = mm(mm(S, h), Si); i = mm(S, i); p = mm(p, Si)
    return dict(degs=degs, udeg=udeg, d=d, h=h, i=i, p=p, n=n, nu=nu)


def rand_graded(X, Y, shift):
    # map X -> Y raising degree by `shift`
    M = zeros(Y['n'], X['n'])
    for r in range(Y['n']):
        for c in range(X['n']):
            if Y['degs'][r] == X['degs'][c] + shift:
                M[r][c] = random.randrange(P)
    return M


def rand_chain(X, Y):
    phi = zeros(Y['nu'], X['nu'])
    for r in range(Y['nu']):
        for c in range(X['nu']):
            if Y['udeg'][r] == X['udeg'][c]:
                phi[r][c] = random.randrange(P)
    s = rand_graded(X, Y, -1)
    return add(add(mm(mm(Y['i'], phi), X['p']), mm(Y['d'], s)), mm(s, X['d']))


results = []


def check(name, ok):
    results.append(ok)
    print(("PASS " if ok else "FAIL ") + name)


ok_contr = ok_chain = ok_a = ok_b = ok_c = True
for trial in range(25):
    X = [make_complex() for _ in range(4)]
    for Xk in X:
        if not iszero(add(mm(Xk['p'], Xk['i']), eye(Xk['nu']), -1)):
            ok_contr = False
        lhs = add(eye(Xk['n']), mm(Xk['i'], Xk['p']), -1)
        rhs = add(mm(Xk['d'], Xk['h']), mm(Xk['h'], Xk['d']))
        if lhs != rhs or not iszero(mm(Xk['d'], Xk['d'])):
            ok_contr = False
    F = rand_chain(X[0], X[1]); G = rand_chain(X[1], X[2]); H = rand_chain(X[2], X[3])
    for (M, A, B) in ((F, X[0], X[1]), (G, X[1], X[2]), (H, X[2], X[3])):
        if mm(B['d'], M) != mm(M, A['d']):
            ok_chain = False
    L_ = lambda M, A, B: mm(mm(B['p'], M), A['i'])
    FL, GL, HL = L_(F, X[0], X[1]), L_(G, X[1], X[2]), L_(H, X[2], X[3])
    K = lambda Gm, Fm, A, Bmid, C: mm(mm(mm(mm(C['p'], Gm), Bmid['h']), Fm), A['i'])
    KGF = K(G, F, X[0], X[1], X[2])
    GFL = L_(mm(G, F), X[0], X[2])
    # (a) on the full models: (GF)_L - G_L F_L = p2 G (1 - i1 p1) F i0 = p2 G (d h + h d) F i0
    lhs = add(GFL, mm(GL, FL), -1)
    rhs = add(mm(mm(mm(mm(X[2]['p'], G), mm(X[1]['d'], X[1]['h'])), F), X[0]['i']),
              mm(mm(mm(mm(X[2]['p'], G), mm(X[1]['h'], X[1]['d'])), F), X[0]['i']))
    if lhs != rhs:
        ok_a = False
    # transferred differentials vanish since p d i = 0 here? check p d i
    for Xk in X:
        if not iszero(mm(mm(Xk['p'], Xk['d']), Xk['i'])):
            ok_a = False
    # (b) the printed identity, with L d - d L interpreted using the source/target small differentials
    KHGF = K(H, mm(G, F), X[0], X[2], X[3])
    KHG_F = K(mm(H, G), F, X[0], X[1], X[3])
    KHG = K(H, G, X[1], X[2], X[3])
    lhs = add(add(add(KHGF, KHG_F, -1), mm(HL, KGF)), mm(KHG, FL), -1)
    # small models have zero differential, so L d - d L = 0 on them: lhs must vanish
    if not iszero(lhs):
        ok_b = False
    # unrestricted version of (b) on X0 (before composing with i0); p3 H d = 0 as U3 has zero differential:
    # p3 H [h2 G F - G h1 F + i2 p2 G h1 F - h2 G i1 p1 F] = p3 H h2 G h1 F d - d p3 H h2 G h1 F
    core = add(add(add(mm(mm(X[2]['h'], G), F), mm(mm(G, X[1]['h']), F), -1),
                   mm(mm(mm(X[2]['i'], X[2]['p']), mm(G, X[1]['h'])), F)),
               mm(mm(mm(X[2]['h'], G), mm(X[1]['i'], X[1]['p'])), F), -1)
    lhs2 = mm(mm(X[3]['p'], H), core)
    Lfull = mm(mm(mm(mm(mm(X[3]['p'], H), X[2]['h']), G), X[1]['h']), F)
    if lhs2 != mm(Lfull, X[0]['d']):
        ok_b = False
    # (c) witness transport: random cycle z in X1 (z = i1 w + d y) and comparison F' = G
    w = [[random.randrange(P)] for _ in range(X[1]['nu'])]
    y = [[random.randrange(P)] for _ in range(X[1]['n'])]
    zc = add(mm(X[1]['i'], w), mm(X[1]['d'], y))
    if not iszero(mm(X[1]['d'], zc)):
        ok_c = False
    lhs = add(mm(mm(X[2]['p'], G), zc), mm(mm(mm(mm(X[2]['p'], G), X[1]['i']), X[1]['p']), zc), -1)
    # on the small model d(...) = 0, so need lhs = 0; verify the unreduced identity on X2 too:
    lhsX = add(mm(G, zc), mm(mm(mm(G, X[1]['i']), X[1]['p']), zc), -1)
    rhsX = mm(mm(mm(X[2]['d'], G), X[1]['h']), zc)
    if lhsX != rhsX or not iszero(lhs):
        ok_c = False

check("contraction data: p i = 1, 1 - i p = d h + h d, d^2 = 0", ok_contr)
check("random F,G,H are chain maps", ok_chain)
check("(a) (GF)_L - G_L F_L = p G (dh+hd) F i  (transferred composition homotopy K = pGhFi)", ok_a)
check("(b) K(H,GF)-K(HG,F)+H_L K(G,F)-K(H,G)F_L = Ld - dL with L = pHhGhFi (printed sign convention)", ok_b)
check("(c) G z - G i p z = d(G h z) for cycles z (witness transport after paragraph 8)", ok_c)
print("\n%d/%d PASS" % (sum(results), len(results)))
