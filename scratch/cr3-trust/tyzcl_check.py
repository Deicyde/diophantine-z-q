"""cr3-trust: end-to-end check of CertifiedRankTYZClRk on 30 inputs (one after another).
Inputs: every 13th of the 386 squarefree d = 5 mod 8 (d < 30000, 3..5 primes) with Lean's T5b = 1
(selection by Redei bits, select.py), i.e. d no. 0, 13, 26, ... (30 values).
For each d:
  * T5bCl(d) from the Lean definition: sum over set partitions of the primes of d with one block = 7,
    one = 3, the others = 1 (mod 8) of prod_B #(Cl(Q(sqrt(-d_B)))^2) mod 2, where Cl is the class
    group of the full ring of integers, from bnfinit(x^2 + d_B) certified by bnfcertify
    (unconditional); #Cl^2 is odd iff no cyclic factor has order divisible by 4;
  * root number of C_d (ellrootno), analytic rank (ellanalyticrank, numerical),
  * a rational point from ellrank (or, when ellrank lists none, a search of the 2-coverings from ell2cover with
    hyperellratpoints up to height 10^5; ellheegner was too slow at these conductors), checked to lie on y^2 = x^3 - d^2 x and to be outside
    C_d(Q)_tors = C_d[2] (elltors), hence of infinite order (exact).
"""
import sys
sys.path.insert(0, "scratch/rv-cr5b-sec3")
import mirror as m
sys.path.insert(0, "scratch/cr3-trust")
from cover_point import cover_point

pari = m.pari

ds = []
for d in range(5, 30000, 8):
    if not pari.issquarefree(d):
        continue
    b = m.Bits(d)
    if 3 <= b.r <= 5 and m.T5b(b)[0] == 1:
        ds.append(d)
assert len(ds) == 386, len(ds)
sample = ds[::13]
print("sample size", len(sample))

cache = {}
def gcl_bit(n):
    if n not in cache:
        bnf = pari.bnfinit(pari("x^2+%d" % n), 1)
        assert int(pari.bnfcertify(bnf)) == 1
        cyc = [int(c) for c in bnf.bnf_get_cyc()]
        cache[n] = 0 if any(c % 4 == 0 for c in cyc) else 1
    return cache[n]

bad = 0
for d in sample:
    P = m.primes_of(d)
    tcl = 0
    for part in m.set_partitions(list(range(len(P)))):
        prods = []
        for B in part:
            x = 1
            for i in B:
                x *= P[i]
            prods.append(x)
        cl = [x % 8 for x in prods]
        if cl.count(7) == 1 and cl.count(3) == 1 and all(c in (7, 3, 1) for c in cl):
            t = 1
            for x in prods:
                t *= gcl_bit(x)
            tcl += t
    tcl %= 2
    E = pari.ellinit([0, 0, 0, -d * d, 0])
    rn = int(pari.ellrootno(E))
    ar = int(pari.ellanalyticrank(E)[0])
    tors = int(pari.elltors(E)[0])
    rk = pari.ellrank(E)
    lo, hi = int(rk[0]), int(rk[1])
    pts = list(rk[3])
    src = "ellrank"
    if not pts:  # ellrank may report r = 1 without a point; then search the 2-coverings
        Q = cover_point(d, bounds=(10**3, 10**4, 10**5))
        pts = [Q] if Q is not None else []
        src = "ell2cover" if pts else "none found"
    ok_pt = False
    for Pt in pts:
        x, y = Pt[0], Pt[1]
        on = (y * y == x ** 3 - d * d * x)
        nontors = not (y == 0)
        ok_pt = ok_pt or (on and nontors)
    good = (tcl == 1 and rn == -1 and ar == 1 and tors == 4 and lo >= 1)  # point reported separately
    bad += (not good)
    print(d, P, "T5bCl=%d rootno=%d anrank=%d #tors=%d ellrank=[%d,%d] nontorsion_point=%s(%s) %s"
          % (tcl, rn, ar, tors, lo, hi, ok_pt, src, "ok" if good else "FAIL"))
    sys.stdout.flush()
print("failures (T5bCl, root number, analytic rank, torsion):", bad, " class groups certified:", len(cache))
