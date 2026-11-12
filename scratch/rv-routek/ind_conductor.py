"""G16, permutation part of Ind: for Galois L/Q and p, the Artin conductor of Ind_{G_L}^{G_Q} 1
(= v_p(disc L), conductor-discriminant formula) is <= [L:Q](1 + u_last), u_last the last upper
break at p.  Ramification groups from PARI's idealramgroups; upper numbering via Herbrand.
Run: ~/pyenv/bin/python ind_conductor.py"""
import cypari2
from fractions import Fraction
pari = cypari2.Pari()
pari.allocatemem(2*10**9)
polys = ["polcyclo(8)", "polcyclo(9)", "polcyclo(16)", "polcyclo(27)", "polcyclo(25)", "polcyclo(12)",
         "x^4-2", "x^3-2", "x^4+2", "x^4-3", "x^3-3", "x^4-12", "x^6+3", "x^4-6", "x^3-12",
         "x^2-2", "x^2+1", "x^4-18", "x^4+8", "x^3-18"]
allok = True
n_checked = 0
for s in polys:
    f = pari(s)
    f = pari.polredbest(pari.nfsplitting(f)) if pari.poldegree(f) > 2 or True else f
    nf = pari.nfinit(f)
    gal = pari.galoisinit(nf)
    n = int(pari.poldegree(f))
    d = int(nf[2])
    for p in [int(q) for q in pari.factor(abs(d))[0]]:
        pr = pari.idealprimedec(nf, p)[0]
        groups = pari.idealramgroups(nf, gal, pr)
        sizes = [int(len(g[0])) if len(g) else 1 for g in groups]   # [G_-1 (decomp), G_0, G_1, ...]
        # pari returns galois subgroups as [gens, orders]; order = product of orders
        sizes = []
        for g in groups:
            o = 1
            for x in list(g[1]): o *= int(x)
            sizes.append(o)
        dec, lower = sizes[0], sizes[1:]       # lower[i] = |G_i|
        e = lower[0]; fdeg = dec // e; g_num = n // dec
        # different exponent (in L_P) delta = sum_{i>=0} (|G_i| - 1); v_p(disc) = g f delta
        delta = sum(x - 1 for x in lower)
        vdisc = g_num * fdeg * delta
        # last lower break i0 = max i with |G_i| > 1; phi(i0) = sum_{j=1}^{i0} |G_j|/|G_0|
        i0 = max(i for i, x in enumerate(lower) if x > 1)
        u_last = sum(Fraction(lower[j], e) for j in range(1, i0 + 1))
        ok = (vdisc == int(pari.valuation(d, p))) and vdisc <= n * (1 + u_last)
        allok &= ok; n_checked += 1
        print(f"{s:12} n={n:3} p={p} e={e} lower={lower} vdisc={vdisc} u_last={u_last} "
              f"bound n(1+u)={float(n*(1+u_last)):.1f} {'OK' if ok else 'FAIL'}")
print("checked", n_checked, "ALL OK:", allok)
