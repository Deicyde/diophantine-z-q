"""Search templates: virtual prime p* (class c mod 8) plus aux q's (classes, symbols) with
dim Sel = 3 and p* a first coordinate (u = e_0), configs as in symsel."""
import sys, os, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "descent-alt"))
from symsel import selmer_dim, has_first

def cfg(classes, upper):
    """classes: list of residues mod 8; upper: dict (i,j) i<j -> [p_j/p_i]; reciprocity fills [p_i/p_j]."""
    k = len(classes)
    lam = [0 if c % 4 == 1 else 1 for c in classes]
    mu = [0 if c % 8 in (1, 7) else 1 for c in classes]
    L = [[0] * k for _ in range(k)]
    for (i, j), x in upper.items():
        L[i][j] = x
        L[j][i] = x ^ (lam[i] & lam[j])
    d = 1
    for c in classes: d = d * c % 8
    return (d, lam, mu, L)

for r in (1, 2):
    for c in (1, 3, 5, 7):
        sols = []
        for qcl in itertools.product((1, 3, 5, 7), repeat=r):
            pairs = [(i, j) for i in range(r + 1) for j in range(i + 1, r + 1)]
            for bits in itertools.product((0, 1), repeat=len(pairs)):
                C = cfg((c,) + qcl, dict(zip(pairs, bits)))
                if selmer_dim(C) == 3 and has_first(C, 1):
                    sols.append((qcl, bits))
        print("r", r, "class p*", c, "#solutions", len(sols), sols[:6])
