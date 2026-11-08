"""For 30 squarefree d with dim Sel_2(C_d) = 3 (computed by sel2cong), find a non-torsion point with
PARI's ellrank and check that the Kummer images of the point and the 2-torsion span exactly the
computed Selmer group (so each Selmer first coordinate is the abscissa class of a rational point)."""
import random
from fractions import Fraction as Fr
import cypari2
from sel2cong import selmer, vec_of, F2Span, kummer

pari = cypari2.Pari()
pari.allocatemem(10 ** 9)


def oddprimes(n):
    return [int(p) for p in pari.factor(abs(n))[0] if int(p) != 2]


def sqf(r):
    r = Fr(r)
    return int(pari.core(r.numerator * r.denominator))


rng = random.Random(4242)
done = 0
agree = 0
tried = set()
while done < 30:
    d = rng.randrange(5, 4000) * rng.choice([1, -1])
    if d in tried or int(pari.issquarefree(d)) == 0:
        continue
    tried.add(d)
    basis, gens = selmer(d, oddprimes(d))
    if len(basis) != 3:
        continue
    E = pari.ellinit([0, 0, 0, -d * d, 0])
    rk = pari.ellrank(E)
    if int(rk[0]) < 1 or len(rk[3]) == 0:
        print(d, "ellrank found no point; bounds", rk[0], rk[1])
        done += 1
        continue
    P = rk[3][0]
    x = Fr(int(pari.numerator(P[0])), int(pari.denominator(P[0])))
    imgs = [kummer(x, d), kummer(0, d), kummer(d, d)]
    sp_img = F2Span()
    for a, b in imgs:
        sp_img.add(vec_of(sqf(a), gens) | (vec_of(sqf(b), gens) << len(gens)))
    sp_sel = F2Span()
    for a, b in basis:
        sp_sel.add(a | (b << len(gens)))
    same = sp_img.dim() == 3 and all(sp_sel.reduce(v) == 0 for v in sp_img.rows.values())
    agree += same
    done += 1
    print(d, "generator x =", x, "image = Selmer:", same)
print("agree", agree, "of", done)
