"""hecke-rest: the computation behind HeckeFibreSizes (twist-fibre sizes 144/36/24/72).

Coordinates: x = n0 + n1 i + n2 (1+j)/2 + n3 (i+k)/2 in O, B = (2,-3) (i^2 = 2, j^2 = -3),
the kernel's ofInt / mulCoord (ZInQKernel/HDecomp/QM/Structures.lean).

Counting model (each step below is checked by brute force):
  a twist fibre = classes of (A, iota o t_k, eta), k in Fin 4, eta a level structure;
  level structures on a fixed pair <-> (O/3O)^x (72); Aut(pair) = com^x acts freely;
  pairs (A, iota o t_k), (A, iota o t_l) isomorphic iff t_l t_k^{-1} = t_m (mod inner)
  with w_m fixing the point.  Size = r * 72 / a, r = 4/|S|, a = |com^x|.
"""
from itertools import product

def mul(n, m):  # mulCoord n m = coordinates of ofInt n * ofInt m
    return (m[0]*n[0] + 2*m[1]*n[1] + 2*m[1]*n[3] - m[2]*n[2] + 2*m[3]*n[3],
            m[0]*n[1] + m[1]*n[0] + m[1]*n[2] - m[2]*n[3] + m[3]*n[2],
            m[0]*n[2] - 2*m[1]*n[3] + m[2]*n[0] + m[2]*n[2] + 2*m[3]*n[1],
            m[0]*n[3] - m[1]*n[2] + m[2]*n[1] + m[2]*n[3] + m[3]*n[0])

def nrd(n):
    return n[0]**2 + n[0]*n[2] + n[2]**2 - 2*(n[1]**2 + n[1]*n[3] + n[3]**2)

def trd(n):  # reduced trace: 2*re = 2 n0 + n2
    return 2*n[0] + n[2]

ONE = (1, 0, 0, 0)
def red(n):
    return tuple(x % 3 for x in n)

# 1. (O/3O)^x
R3 = list(product(range(3), repeat=4))
U72 = [c for c in R3 if nrd(c) % 3 != 0]
units_mod3 = [c for c in R3 if any(red(mul(c, d)) == ONE for d in R3)]
print("1. |O/3O| =", len(R3), " |(O/3O)^x| =", len(units_mod3),
      " = #{nrd != 0 mod 3}:", sorted(units_mod3) == sorted(U72))

# 2. CM elements in O (search box) and their unit groups
box = range(-4, 5)
def find(pred):
    return [n for n in product(box, repeat=4) if pred(n)]
sq = lambda n: mul(n, n)
x4 = find(lambda n: sq(n) == (-1, 0, 0, 0))                     # x^2 = -1
x3 = find(lambda n: tuple(a - b + c for a, b, c in zip(sq(n), n, ONE)) == (0, 0, 0, 0))  # x^2-x+1=0
x24 = find(lambda n: sq(n) == (-6, 0, 0, 0))                    # x^2 = -6
print("2. elements with x^2=-1:", len(x4), "e.g.", x4[0],
      "| x^2-x+1=0:", len(x3), "e.g.", x3[0], "| x^2=-6:", len(x24), "e.g.", x24[0])

def cyc(x):
    g, out = ONE, []
    while True:
        out.append(g); g = mul(g, x)
        if g == ONE: return out
G4 = cyc(x4[0]); G6 = cyc(x3[0]); G2 = [ONE, (-1, 0, 0, 0)]
print("   unit groups: |<i>| =", len(G4), " |<zeta6>| =", len(G6), " |{+-1}| =", len(G2))

# 3. finite-order units are not = 1 mod 3O (norm of x-1 in {1,2,3,4}, elements of 3O have 9 | nrd)
bad = [g for G in (G4, G6, G2) for g in G if g != ONE and red(g) == ONE]
print("3. nontrivial finite-order units = 1 mod 3O:", bad,
      " nrd(g-1):", sorted({nrd(tuple(a - b for a, b in zip(g, ONE))) for G in (G4, G6, G2) for g in G if g != ONE}))

# 4. free right action on (O/3O)^x, orbit counts 72/a
def orbits(G):
    seen, cnt = set(), 0
    for c in U72:
        if c in seen: continue
        cnt += 1
        for g in G: seen.add(red(mul(c, g)))
    return cnt
def free(G):
    return all(red(mul(c, g)) != c for c in U72 for g in G if g != ONE)
print("4. orbits on (O/3O)^x: CM4", orbits(G4), "CM3", orbits(G6), "generic/CM24", orbits(G2),
      "| free:", free(G4), free(G6), free(G2))

# 5. Atkin-Lehner fixed points: elliptic mu in O with nrd(mu) = m (m = 2, 3, 6),
#    trace t, t^2 < 4m: the CM field Q(sqrt(t^2-4m)) must embed in B (2, 3 non-split).
def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1)//2, p) == 1 else -1
def splits(d, p):  # does p split in Q(sqrt d)?  d squarefree-ish discriminant
    if p == 2:
        return d % 8 == 1
    return legendre(d, p) == 1
def sqfree(d):
    s = 1 if d > 0 else -1; d = abs(d); out = 1; f = 2
    while f*f <= d:
        while d % (f*f) == 0: d //= f*f
        f += 1
    return s*d
print("5. elliptic normalizer elements mu in O of norm m (w_m):")
for m in (2, 3, 6):
    for t in range(0, 5):
        if t*t >= 4*m: continue
        D = t*t - 4*m
        d = sqfree(D)
        dd = d if d % 4 == 1 else 4*d
        emb = not splits(dd, 2) and not splits(dd, 3)
        ex = find(lambda n: nrd(n) == m and trd(n) == t)
        print(f"   m={m} t={t}: disc {D}, field Q(sqrt {d}), embeds in B: {emb}, "
              f"elements in box: {len(ex)}")

# 6. composition of the representatives t_k = conj(1, i, j, ij): tt_k tt_l = c * tt_{k xor l}
tt = [ONE, (0, 1, 0, 0), (-1, 0, 2, 0), mul((0, 1, 0, 0), (-1, 0, 2, 0))]
def scalar_multiple(a, b):  # a = c b for rational c (b has some nonzero coord)
    for i in range(4):
        if b[i] != 0:
            from fractions import Fraction
            c = Fraction(a[i], b[i])
            return all(Fraction(a[j]) == c*b[j] for j in range(4)), c
    return False, None
ok = all(scalar_multiple(mul(tt[k], tt[l]), tt[k ^ l])[0] for k in range(4) for l in range(4))
print("6. tt_k * tt_l is a rational multiple of tt_(k xor l) for all k, l:", ok)

# 7. the sizes
for name, a, S in (("generic", 2, 1), ("CM4", 4, 2), ("CM3", 6, 2), ("CM24", 2, 2)):
    r = 4 // S
    print(f"7. {name}: a=|com^x|={a}, |S|={S}, r={r}, fibre size r*72/a = {r*72//a},"
          f" 144 | (4,6,2)*size: {[(k*r*72//a) % 144 == 0 for k in (4, 6, 2)]}")
