r"""hfx-proof: witness tables for the merges (and a check of the root non-merges).
Hurwitz coordinates H4: x = a0 + a1 i + a2 j + a3 zeta, zeta = (-1+i+j+k)/2 (t21's hc/mulH/nrdH)."""
from itertools import product

def mulH(a, b):
    a0,a1,a2,a3 = a; b0,b1,b2,b3 = b
    return (-a3*b3 - a3*b1 - a2*b3 - a2*b2 - a2*b1 + a1*b2 - a1*b1 + a0*b0,
            -a3*b2 + a2*b3 + a2*b1 - a1*b3 - a1*b2 + a1*b0 + a0*b1,
            -a3*b2 + a3*b1 + a2*b1 + a2*b0 - a1*b3 - a1*b2 + a0*b2,
            -a3*b3 + a3*b2 - a3*b1 + a3*b0 - a2*b3 - 2*a2*b1 + a1*b3 + 2*a1*b2 + a0*b3)
def starH(a): return (a[0]-a[3], -a[1], -a[2], -a[3])
def nrdH(a):
    a0,a1,a2,a3 = a
    return a3*a3 + a2*a3 + a2*a2 + a1*a3 + a1*a1 - a0*a3 + a0*a0
def md(a, m): return tuple(x % m for x in a)
def add(a, b): return tuple(x+y for x,y in zip(a,b))
def sub(a, b): return tuple(x-y for x,y in zip(a,b))
def sm(s, a): return tuple(s*x for x in a)
unitList = [(-1,0,0,0),(0,-1,0,0),(0,0,-1,0),(-1,1,1,-2),(1,-1,-1,2),(0,0,1,0),(0,1,0,0),(1,0,0,0),
   (1,0,0,1),(0,1,1,-1),(1,0,-1,1),(0,1,0,-1),(1,-1,0,1),(0,0,1,-1),(1,-1,-1,1),(0,0,0,-1),
   (0,0,0,1),(-1,1,1,-1),(0,0,-1,1),(-1,1,0,-1),(0,-1,0,1),(-1,0,1,-1),(0,-1,-1,1),(-1,0,0,-1)]
assert all(nrdH(u) == 1 for u in unitList)
T8 = list(product(range(2), repeat=3))
def betaZ(t): return (1, 2*t[0], 2*t[1], 2*t[2])
oneI = (1,1,0,0)

def hc_of_pure(a, b, c):   # hc of a i + b j + c k
    return (c, a - c, b - c, 2*c)

def find_witness(W, t, r, unif_ok, mod):
    """alpha = x + y*W (Hurwitz coords), rho = oneI^bb * s * mu; need conj(A)(B-A) = 0 mod 4*2^bb,
    A = rho*beta_r, B = beta_t*alpha."""
    for x, y in product(range(mod), repeat=2):
        alpha = add((x,0,0,0), sm(y, W))
        na = nrdH(alpha)
        if na % 2 == 1: bb = 0
        elif unif_ok and na % 4 == 2: bb = 1
        else: continue
        B = mulH(betaZ(t), alpha)
        for i, mu in enumerate(unitList):
            for s in (1, -1):
                rho = sm(s, mu) if bb == 0 else mulH(oneI, sm(s, mu))
                A = mulH(rho, betaZ(r))
                C = mulH(starH(A), sub(B, A))
                if all(z % (4 * 2**bb) == 0 for z in C):
                    return (x, y, i, 0 if s == 1 else 1, bb)
    return None

# ---------- n = 3 mod 8 : W = hc(omega), omega = (1 + a i + b j + c k)/2, a,b,c odd
res3 = {}
for a, b, c in product(range(1, 8, 2), repeat=3):
    W = ((1 + c)//2, (a - c)//2, (b - c)//2, c)
    key = md(W, 4)
    if key in res3: continue
    # classes: connected via witnesses to roots; first find which t are in the class of 0
    cls0 = [t for t in T8 if find_witness(W, t, (0,0,0), False, 4) is not None]
    other = [t for t in T8 if t not in cls0]
    r1 = other[0]
    ok = all(find_witness(W, t, r1, False, 4) is not None for t in other)
    res3[key] = (cls0, other, ok)
print("n=3: residues", len(res3), "class sizes", {(len(v[0]), len(v[1]), v[2]) for v in res3.values()})

# ---------- n = 1 mod 8 : omega = a i + b j + c k, 4 | c, one of a,b odd, other = 0 mod 4
res1 = {}
for a, b, c in product(range(8), repeat=3):
    if c % 4 or (a*a + b*b + c*c) % 8 != 1: continue
    W = hc_of_pure(a, b, c)
    key = md(W, 8)
    if key in res1: continue
    roots = [(0,0,0), (1,1,0), (1,0,1)]
    assign = {}
    for t in T8:
        for r in roots:
            if find_witness(W, t, r, True, 8) is not None:
                assign.setdefault(t, []).append(r)
    res1[key] = assign
print("n=1: residues", len(res1))
print({tuple(tuple(v) for v in d.values()) for d in res1.values()})

def rel_exists(W, t, tp, unif):
    """exists mu, X, Y (mod 4): beta_t * e == (oneI^unif) mu beta_tp (X + Y W) mod 4, e = 1 or 1 + omega"""
    lhs = betaZ(t) if not unif else mulH(betaZ(t), add((1,0,0,0), W))
    lhs = md(lhs, 4)
    for mu in unitList:
        pre = mulH(mu, betaZ(tp))
        if unif: pre = mulH(oneI, pre)
        for X, Y in product(range(4), repeat=2):
            if md(mulH(pre, add((X,0,0,0), sm(Y, W))), 4) == lhs:
                return True
    return False

bad = 0
for key, (c0, oth, ok) in res3.items():
    W = key
    r = oth[0] if (0,0,0) in c0 else c0[0]
    if rel_exists(W, r, (0,0,0), False): bad += 1
print("n=3 non-merge failures:", bad)
bad = 0
for key, assign in res1.items():
    W = key
    o2 = [t for t in T8 if assign[t] == [(1,1,0)]]
    r2 = (1,1,0)
    for (t, tp) in [(r2, (0,0,0)), ((1,0,1), (0,0,0)), ((1,0,1), r2)]:
        for unif in (False, True):
            if rel_exists(W, t, tp, unif): bad += 1; print("fail", key, t, tp, unif)
print("n=1 non-merge failures:", bad)

oneMI = (1,-1,0,0)
def rel2_exists(W, t, tp):
    """exists mu, X, Y: (1-i) beta_t (1+omega) == 2 mu beta_tp (X + Y omega) mod 8"""
    lhs = md(mulH(oneMI, mulH(betaZ(t), add((1,0,0,0), W))), 8)
    for mu in unitList:
        pre = sm(2, mulH(mu, betaZ(tp)))
        for X, Y in product(range(4), repeat=2):
            if md(mulH(pre, add((X,0,0,0), sm(Y, W))), 8) == lhs:
                return True
    return False
bad = 0
for key, assign in res1.items():
    W = key
    r2 = (1,1,0)
    for (t, tp) in [(r2, (0,0,0)), ((1,0,1), (0,0,0)), ((1,0,1), r2)]:
        if rel_exists(W, t, tp, False): bad += 1; print("fail1", key, t, tp)
        if rel2_exists(W, t, tp): bad += 1; print("fail2", key, t, tp)
print("n=1 refined non-merge failures:", bad)
