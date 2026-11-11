"""Independent sample check of TYZRow5b and TYZThm35ReadingA as Lean states them:
T5bCl d = Σ over set partitions of the primes of d with one block ≡7, one ≡3, rest ≡1 (mod 8) of Π #2Cl(Q(√-d_B)) mod 2,
T5aCl d = same with one block ≡5, rest ≡1. Check: T5b odd ⇒ analytic rank 1; analytic rank ≥ 2 ⇒ T5a, T5b even.
Sample: 26565, 33117 (rank 3, nt-tyz §1.4) and the first 28 squarefree d ≡ 5 (mod 8) with ≥ 2 primes ≡ 3, 7 (mod 8)."""
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
def g(m):  # #2Cl(Q(sqrt(-m))) = h / #Cl[2]
    D = -m if m % 4 == 3 else -4*m
    cyc = [int(c) for c in pari.quadclassunit(D)[1]]
    h = 1
    for c in cyc: h *= c
    return h // 2**sum(1 for c in cyc if c % 2 == 0)
def partitions(s):
    if not s: yield []; return
    first, rest = s[0], s[1:]
    for p in partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i+1:]
        yield [[first]] + p
def prod(B):
    r = 1
    for x in B: r *= x
    return r
def T(d, row):
    ps = [int(p) for p in pari.factor(d)[0]]; tot = 0
    for P in partitions(ps):
        cl = [prod(B) % 8 for B in P]
        if row == 'b': ok = cl.count(7) == 1 and cl.count(3) == 1 and all(c in (1,3,7) for c in cl)
        else: ok = cl.count(5) == 1 and all(c in (1,5) for c in cl)
        if ok:
            w = 1
            for B in P: w *= g(prod(B))
            tot += w
    return tot % 2
ds = [26565, 33117]; d = 5
while len(ds) < 30:
    if pari.issquarefree(d) and sum(1 for p in pari.factor(d)[0] if int(p) % 8 in (3, 7)) >= 2: ds.append(d)
    d += 8
bad = 0
for d in ds:
    E = pari.ellinit([0, 0, 0, -d*d, 0]); r = int(pari.ellanalyticrank(E)[0])
    t5a, t5b = T(d, 'a'), T(d, 'b')
    viol = (t5b == 1 and r != 1) or (r >= 2 and (t5a or t5b))
    bad += viol
    print(d, [int(p) for p in pari.factor(d)[0]], 'rank', r, 'T5a', t5a, 'T5b', t5b, 'VIOLATION' if viol else '')
print('samples', len(ds), 'violations', bad)
