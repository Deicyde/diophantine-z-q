r"""hfx-proof: orbit structure of K_{n,2}^x on TYZ's 8 classes O_B^x \ (O_B/4)^x / {+-1},
for every residue of tau(sqrt(-n)) = a i + b j + c k mod 8 allowed by AdmissibleTau.
Quaternions stored as doubled coordinates (A,B,C,D) = 2*(re, i, j, k), all same parity."""
from itertools import product

def qmul(p, q):  # doubled * doubled -> doubled  (P/2)(Q/2) = R/2, R = PQ/2
    a1,b1,c1,d1 = p; a2,b2,c2,d2 = q
    r = (a1*a2-b1*b2-c1*c2-d1*d2, a1*b2+b1*a2+c1*d2-d1*c2, a1*c2-b1*d2+c1*a2+d1*b2, a1*d2+b1*c2-c1*b2+d1*a2)
    assert all(x % 2 == 0 for x in r), (p,q,r)
    return tuple(x//2 for x in r)
def nrd(q): s = sum(x*x for x in q); assert s % 4 == 0; return s//4
def coords(q):
    a,b,c,d = q; return ((a+d)//2, (b-d)//2, (c-d)//2, d)
def from_coords(x):
    x0,x1,x2,x3 = x; return (2*x0-x3, 2*x1+x3, 2*x2+x3, x3)
def red(q): return tuple(t % 4 for t in coords(q))
UNITS4 = [x for x in product(range(4), repeat=4) if nrd(from_coords(x)) % 2 == 1]
OBX = [q for q in product(range(-2,3), repeat=4) if all((t-q[0])%2==0 for t in q) and sum(t*t for t in q)==4]
def m4(x, y): return red(qmul(from_coords(x), from_coords(y)))
cls = {}; reps = []
for x in UNITS4:
    if x in cls: continue
    for u in OBX:
        for s in (1, -1):
            cls[m4(red(u), tuple((s*t) % 4 for t in x))] = len(reps)
    reps.append(x)
assert len(reps) == 8
def two_rep(t):
    a,b,c = t; return red((2-2*c, 4*a+2*c, 4*b+2*c, 2*c))   # 1+2x = (1-c) + (2a+c)i + (2b+c)j + ck, doubled
TR = {t: cls[two_rep(t)] for t in product(range(2), repeat=3)}
assert sorted(TR.values()) == list(range(8))
inv = {v: k for k, v in TR.items()}

def orbits(gens_maps):
    parent = list(range(8))
    def find(i):
        while parent[i] != i: i = parent[i]
        return i
    for g in gens_maps:
        for c in range(8):
            a, b = find(c), find(g(c))
            if a != b: parent[a] = b
    groups = {}
    for c in range(8): groups.setdefault(find(c), []).append(inv[c])
    return sorted(groups.values(), key=len)

def unit_gens(abc):
    a,b,c = abc
    sq = (0, 2*a, 2*b, 2*c)       # tau(sqrt(-n)) doubled
    out = []
    for u, v in product(range(8), repeat=2):
        # (u + v sqrt(-n)) / 2 ? only integral O_K elements: for n=3 mod 8, O_K = Z[(1+sqrt)/2]
        q = (u, v*2*a//2 if False else v*a, v*b, v*c)  # doubled coords of (u + v*sqrt(-n))/2
        if not all((t - q[0]) % 2 == 0 for t in q): continue
        if nrd(q) % 2 == 1:
            g = red(q)
            out.append(lambda cc, g=g: cls[m4(reps[cc], g)])
    return out

PI = (2, 2, 0, 0)   # 1+i doubled
PIINV_num = (2, -2, 0, 0)  # 1-i doubled; (1+i)^{-1} = (1-i)/2
def unif_map(abc):
    a,b,c = abc
    w = (2, 2*a, 2*b, 2*c)   # 1 + tau(sqrt(-n)) doubled
    def g(cc):
        x = from_coords(reps[cc])
        y = qmul(qmul(PIINV_num, x), w)   # (1-i) x w, doubled
        assert all(t % 2 == 0 for t in y)
        y = tuple(t//2 for t in y)        # /2
        assert nrd(y) % 2 == 1
        return cls[red(y)]
    return g

res = {}
for abc in product(range(8), repeat=3):
    a,b,c = abc
    n8 = (a*a+b*b+c*c) % 8
    if n8 == 3 and a % 2 and b % 2 and c % 2:
        o = orbits(unit_gens(abc)); res[('3', abc)] = o
    if n8 == 1 and c % 4 == 0:
        o = orbits(unit_gens(abc) + [unif_map(abc)]); res[('1', abc)] = o
from collections import Counter
print(Counter(tuple(len(g) for g in o) for o in res.values()))
for k, o in list(res.items())[:6]: print(k, o)
print("--- without uniformizer, n=1 mod 8")
print(Counter(tuple(len(g) for g in orbits(unit_gens(abc))) for (k, abc) in res if k == '1'))
# which (a,b,c) mod 8 classes for n = 3 give which t*
ts = Counter()
for (k, abc), o in res.items():
    if k == '3': ts[tuple(o[0])] += 1
print(ts)
