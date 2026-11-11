"""Rank guard on the kept curves C_d : y^2 = x^3 - d^2 x of slots.json (d = d1, d2).

Per curve: ellrootno; ellanalyticrank if d < 2*10^6 (real precision 19, as cr3-check/anrank.py);
ellrank at effort 0, 1, 2, 3 (stop as soon as r1 = r2 and r1 points are found); Kummer images (sqf x, sqf(x - d)) of the
points found and of the 2-torsion ((0,0) -> (-1, -d), (d,0) -> (d, 2), (-d,0) -> (-d, -2d) up to
squares); test whether beta is the first coordinate of an element of their F2-span.
Usage: python curves.py slots.json > curves.json"""
import sys, json
import cypari2
pari = cypari2.Pari(); pari.allocatemem(4 * 10 ** 9)
pari.set_real_precision(19)


def core(r):
    return int(pari.core(pari.numerator(r) * pari.denominator(r)))


def kummer(P, d):
    x = P[0]
    return core(x), core(x - d)


def vec(n, basis):
    """F2 vector of the squarefree n over basis (-1 first, then primes)."""
    v = [1 if n < 0 else 0]
    n = abs(n)
    for p in basis[1:]:
        if n % p == 0:
            v.append(1); n //= p
        else:
            v.append(0)
    assert n == 1
    return v


def first_coord_in_span(pairs, beta, basis):
    """Is there a subset product of `pairs` with first coordinate = beta mod squares?"""
    rows = [vec(a, basis) + vec(b, basis) for a, b in pairs]
    k = len(basis)
    import itertools
    target = vec(beta, basis)
    for c in itertools.product((0, 1), repeat=len(rows)):
        s = [0] * k
        for ci, r in zip(c, rows):
            if ci:
                s = [(x + y) % 2 for x, y in zip(s, r[:k])]
        if s == target:
            return True
    return False


def check(d, beta):
    E = pari.ellinit([-d * d, 0])
    rec = dict(d=d, beta=beta, rootno=int(pari.ellrootno(E)))
    if d < 2 * 10 ** 6:
        ar = pari.ellanalyticrank(E)
        rec["anrank"] = int(ar[0]); rec["Lderiv"] = str(ar[1])
    for eff in range(4):
        r1, r2, s, L = pari.ellrank(E, eff)
        if int(r1) == int(r2) and len(L) == int(r1):
            break
    rec.update(effort=eff, r1=int(r1), r2=int(r2), s=int(s),
               gens=[[str(P[0]), str(P[1])] for P in L])
    for P in L:
        assert pari.ellisoncurve(E, P)
    basis = [-1, 2] + sorted(int(p) for p in pari.factor(d)[0])
    tors = [(-1, core(-d)), (core(d), 2), (core(-d), core(-2 * d))]
    imgs = [kummer(P, d) for P in L]
    rec["kummer"] = imgs
    rec["beta_in_span"] = first_coord_in_span(imgs + tors, beta, basis) if L else None
    rec["beta_in_tors"] = first_coord_in_span(tors, beta, basis)
    return rec


if __name__ == "__main__":
    out = []
    for r in json.load(open(sys.argv[1])):
        if not r["small"]:
            continue
        for role, d in (("d1", r["d1"]), ("d2", r["d2"])):
            c = check(d, r["beta"])
            c.update(i=r["i"], role=role, primes=sorted(int(p) for p in pari.factor(d)[0]))
            out.append(c)
            print(c, file=sys.stderr, flush=True)
    json.dump(out, sys.stdout, indent=0)
