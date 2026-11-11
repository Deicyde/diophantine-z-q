"""Slots for the pairs of pairs.json with slotk.construct, the smallest admissible prime per slot.

slotk.prime_with is replaced by a search over q = 3, 11, 19, ... (q = cls8 mod 8) in increasing
order; the constraints are those of slotk (symbols [q/p] at P u T, [x/q] at the earlier slots).
Each slot choice is then re-checked field by field against the Lean structure RouteK.Slots
(ZInQKernel/RouteK/Slots/Construction.lean), with legBit p a = bit of the Legendre symbol (a/p),
p0 = smallest prime of beta (slotk's P[0]).  Also the facts of slots_d2_facts: d % 8 = 5, d
squarefree, beta | d, and the Selmer certificate (sel2cong exact 2-descent: dim 3, beta in pi1).
Usage: python slots.py pairs.json > slots.json"""
import os, sys, json
from math import prod
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "slot-k"))
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2 * 10 ** 9)
import slotk
from sel2cong import selmer, vec_of, first_coord_contains

kr = pari.kronecker
slotk.JAC = lambda x, q: int(kr(x, q))


def bit(a, p):
    """legBit p a: 0 if (a/p) = 1, 1 if (a/p) = -1 (p odd prime not dividing a)."""
    k = int(kr(a, p))
    assert k != 0, (a, p)
    return 0 if k == 1 else 1


def prime_with_smallest(cls8, symbols, avoid, search=None, rng=None):
    search = search or {}
    q = cls8 % 8
    while True:
        if q > 2 and q not in avoid and slotk.is_prime(q) and \
                all(q % p and bit(q, p) == e for p, e in symbols.items()) and \
                all(x % q and bit(x, q) == b for x, b in search.items()):
            return q
        q += 8


slotk.prime_with = prime_with_smallest


def fac(n):
    n = abs(int(n))
    if n <= 1:
        return {}
    F = pari.factor(n)
    return {int(p): int(e) for p, e in zip(F[0], F[1])}


def check_slots(beta, theta, p0, q0, rP, rT):
    """All fields of RouteK.Slots beta theta p0 (rP: dict p -> r_p, rT: dict l -> r_l)."""
    P, T = sorted(fac(beta)), sorted(fac(theta))
    G = [p for p in P if p != p0]
    s = 1 if beta < 0 else 0
    x = (s + 1) % 2
    lam = {p: 1 if p % 4 == 3 else 0 for p in P}
    ok = []
    nd = lambda q: (2 * beta * theta) % q != 0
    ok += [slotk.is_prime(q0), q0 % 8 == 3, nd(q0)]
    ok += [bit(q0, p) == (1 + lam[p] * x) % 2 for p in G]
    ok += [bit(q0, p0) == (x + sum(1 + lam[p] * x for p in G)) % 2]
    ok += [bit(q0, l) == 0 for l in T]
    for p in G:
        r = rP[p]
        ok += [slotk.is_prime(r), r % 8 == 1, nd(r), r != q0, bit(r, p) == 1, bit(r, p0) == 1]
        ok += [bit(r, y) == 0 for y in P if y not in (p, p0)]
        ok += [bit(r, l) == 0 for l in T]
        ok += [bit(r, q0) == 0]
        ok += [bit(r, rP[p2]) == 0 for p2 in G if p2 != p]
    ok += [len(set(rP.values())) == len(G)]
    for l in T:
        r = rT[l]
        ok += [slotk.is_prime(r), r % 8 == 1, nd(r), r != q0, bit(r, l) == 1, bit(r, q0) == 1]
        ok += [r != rP[p] for p in G]
        ok += [bit(r, p) == 0 for p in P]
        ok += [bit(r, l2) == 0 for l2 in T if l2 != l]
        ok += [bit(r, rP[p]) == 0 for p in G]
        ok += [bit(r, rT[l2]) == 0 for l2 in T if l2 != l]
    ok += [len(set(rT.values())) == len(T)]
    return all(ok), len(ok)


def d_facts(d, beta):
    """d % 8 = 5, squarefree, beta | d, SelmerCertified d beta (exact 2-descent)."""
    f = fac(d)
    sqf = all(e == 1 for e in f.values())
    basis, gens = selmer(d, sorted(p for p in f if p != 2))
    cert = len(basis) == 3 and first_coord_contains(basis, vec_of(beta, gens))
    return dict(mod8=d % 8, sqf=sqf, beta_div=d % abs(beta) == 0, sel_dim=len(basis), beta_in_pi1=cert)


if __name__ == "__main__":
    pairs = json.load(open(sys.argv[1]))
    out = []
    for i, r in enumerate(pairs):
        beta, theta = r["beta"], r["theta"]
        P, T = sorted(fac(beta)), sorted(fac(theta))
        q0, RP, RT = slotk.construct(beta, theta, P, T)
        rP, rT = dict(zip(P[1:], RP)), dict(zip(T, RT))
        sl_ok, nchecks = check_slots(beta, theta, P[0], q0, rP, rT)
        d1 = abs(beta) * q0 * prod(RP) * prod(RT)
        d2 = d1 * theta
        rec = dict(i=i, m=r["m"], beta=beta, theta=theta, P=P, T=T, q0=q0, RP=RP, RT=RT,
                   slots_ok=sl_ok, nchecks=nchecks, d1=d1, d2=d2, small=d1 < 10 ** 12 and d2 < 10 ** 12)
        if rec["small"]:
            rec["facts1"] = d_facts(d1, beta)
            rec["facts2"] = d_facts(d2, beta)
        out.append(rec)
        print(i, beta, theta, "q0", q0, "RP", RP, "RT", RT, "slots_ok", sl_ok, nchecks,
              "d1", d1, "d2", d2, rec.get("facts1"), rec.get("facts2"), file=sys.stderr, flush=True)
    json.dump(out, sys.stdout, indent=0)
