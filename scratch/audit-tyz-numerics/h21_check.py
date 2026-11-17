# Independent numerical check of the Lean statement TYZThm21PairsC (h21C).
# Mirrors the Lean definitions: Hurwitz order O_B, U = Z_2^x (1+4 O_{B,2}) at 2, U_n = R_n^x K_{n,2}^x,
# InPiZ (left B^x, right U_n, centre, orthogonal to 1 and chi0 o nrd on the 8 classes), IsTestVector = primitive
# generator, quadPeriod = sum over Cl(K) of chi_T(t) f(tau^(t)), chi_q([a]) = (N a / q).
import sys
from fractions import Fraction as Fr
from itertools import product
from math import gcd, isqrt

def qmul(p, q):
    a1,b1,c1,d1 = p; a2,b2,c2,d2 = q
    return (a1*a2 - b1*b2 - c1*c2 - d1*d2,
            a1*b2 + b1*a2 + c1*d2 - d1*c2,
            a1*c2 - b1*d2 + c1*a2 + d1*b2,
            a1*d2 + b1*c2 - c1*b2 + d1*a2)
def qconj(p): return (p[0], -p[1], -p[2], -p[3])
def nrd(p): return sum(x*x for x in p)
def qinv(p):
    n = nrd(p); c = qconj(p); return tuple(x/n for x in c)
def qsub(p,q): return tuple(x-y for x,y in zip(p,q))
def qadd(p,q): return tuple(x+y for x,y in zip(p,q))
def Q(*t): return tuple(Fr(x) for x in t)

def hcoords(q):
    # q = a + b i + c j + e zeta, zeta = (-1+i+j+k)/2
    re,x,y,z = q
    e = 2*z; a = re + z; b = x - z; c = y - z
    return (a,b,c,e)
def is_hurwitz(q):
    return all(Fr(t).denominator == 1 for t in hcoords(q))
def from_h(a,b,c,e):
    return (Fr(a) - Fr(e,2), Fr(b) + Fr(e,2), Fr(c) + Fr(e,2), Fr(e,2))
def key4(q):
    assert is_hurwitz(q), q
    return tuple(int(t) % 4 for t in hcoords(q))
def neg(q): return tuple(-x for x in q)
def xkey(q):
    return min(key4(q), key4(neg(q)))

UNITS = [Q(*t) for t in [(1,0,0,0),(-1,0,0,0),(0,1,0,0),(0,-1,0,0),(0,0,1,0),(0,0,-1,0),(0,0,0,1),(0,0,0,-1)]]
for s in product([1,-1], repeat=4):
    UNITS.append(tuple(Fr(x,2) for x in s))
assert len(UNITS) == 24 and all(nrd(u) == 1 for u in UNITS)

# X = (O_B/4)^x / {+-1}; left orbits under the 24 units
elems = {}
for t in product(range(4), repeat=4):
    q = from_h(*t)
    if nrd(q) % 2 == 1:
        elems[xkey(q)] = from_h(*xkey(q))
assert len(elems) == 96, len(elems)
orbit_of = {}
orbits = []
for k, q in elems.items():
    if k in orbit_of: continue
    orb = set(xkey(qmul(u, q)) for u in UNITS)
    idx = len(orbits); orbits.append(sorted(orb))
    for kk in orb: orbit_of[kk] = idx
assert len(orbits) == 8 and all(len(o) == 12 for o in orbits), [len(o) for o in orbits]
def cls(q): return orbit_of[xkey(q)]
chi0 = []
for o in orbits:
    vals = set(int(nrd(from_h(*k))) % 4 for k in o)
    assert len(vals) == 1
    chi0.append(1 if vals.pop() == 1 else -1)

# Lean's representatives twoRepQ t = <1-c, 2a+c, 2b+c, c>, chi0Rep = (-1)^c
leanreps = {}
for a,b,c in product(range(2), repeat=3):
    q = Q(1-c, 2*a+c, 2*b+c, c)
    leanreps[(a,b,c)] = cls(q)
    assert chi0[cls(q)] == (-1)**c
assert len(set(leanreps.values())) == 8, "Lean's 8 representatives are not a transversal"

def hround(q):
    # nearest Hurwitz quaternion
    c1 = tuple(Fr(round(x)) for x in q)
    c2 = tuple(Fr(round(x - Fr(1,2))) + Fr(1,2) for x in q)
    return c1 if nrd(qsub(q,c1)) <= nrd(qsub(q,c2)) else c2
def rgen(a, b):
    # generator g of the right ideal a O + b O
    zero = Q(0,0,0,0)
    while b != zero:
        q = hround(qmul(qinv(b), a))
        r = qsub(a, qmul(b, q))
        assert nrd(r) < nrd(b)
        a, b = b, r
    return a

def jacobi(a, n):
    a %= n; r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3,5): r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: r = -r
        a %= n
    return r if n == 1 else 0

def primes_of(n):
    ps = []; p = 2; m = n
    while p*p <= m:
        if m % p == 0:
            ps.append(p)
            while m % p == 0: m //= p
        p += 1
    if m > 1: ps.append(m)
    return ps

def reduced_forms(D):
    forms = []
    a = 1
    while 3*a*a <= -D:
        for b in range(-a, a+1):
            if (b*b - D) % (4*a) == 0:
                c = (b*b - D)//(4*a)
                if c < a: continue
                if (abs(b) == a or a == c) and b < 0: continue
                if gcd(gcd(a,abs(b)),c) == 1: forms.append((a,b,c))
        a += 1
    return forms

def egcd(a, b):
    if b == 0: return (a, 1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a//b)*y)

def tunnell(n):
    A = B = 0
    r = isqrt(n)
    for x in range(-r, r+1):
        for y in range(-r, r+1):
            rem = n - x*x - 2*y*y
            if rem < 0: continue
            if rem % 32 == 0:
                z2 = rem//32; z = isqrt(z2)
                if z*z == z2: A += 1 if z == 0 else 2
            if rem % 8 == 0:
                z2 = rem//8; z = isqrt(z2)
                if z*z == z2: B += 1 if z == 0 else 2
    assert B % 2 == 0
    return A - B//2

def nullspace(rows, nv):
    M = [[Fr(x) for x in r] for r in rows]
    piv = []; r = 0
    for c in range(nv):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0: p = i; break
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][c] for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f*y for x,y in zip(M[i], M[r])]
        piv.append(c); r += 1
        if r == len(M): break
    free = [c for c in range(nv) if c not in piv]
    basis = []
    for fc in free:
        v = [Fr(0)]*nv; v[fc] = Fr(1)
        for i, pc in enumerate(piv): v[pc] = -M[i][fc]
        basis.append(v)
    return basis

def test_vector(n, tauS):
    # tauS = tau(sqrt(-n)) as pure quaternion (0,A,B,C)
    rows = []
    if n % 4 == 3:
        om = tuple(x/2 for x in qadd(Q(1,0,0,0), tauS))  # (1+sqrt(-n))/2
    else:
        om = tauS
    assert is_hurwitz(om)
    for x, y in product(range(4), repeat=2):
        k = qadd(Q(x,0,0,0), tuple(y*t for t in om))
        if nrd(k) % 2 == 0: continue
        for o in range(8):
            v = from_h(*orbits[o][0])
            o2 = cls(qmul(v, k))
            if o2 != o:
                row = [0]*8; row[o] = 1; row[o2] = -1; rows.append(row)
    if n % 8 == 1:
        pi = qadd(Q(1,0,0,0), tauS)
        assert nrd(pi) % 4 == 2
        inv1i = qinv(Q(1,1,0,0))
        for o in range(8):
            v = from_h(*orbits[o][0])
            w = qmul(inv1i, qmul(v, pi))
            assert is_hurwitz(w) and nrd(w) % 2 == 1
            # well-definedness on the orbit
            for kk in orbits[o]:
                w2 = qmul(inv1i, qmul(from_h(*kk), pi))
                assert cls(w2) == cls(w)
            o2 = cls(w)
            if o2 != o:
                row = [0]*8; row[o] = 1; row[o2] = -1; rows.append(row)
    rows.append([1]*8)
    rows.append(list(chi0))
    ns = nullspace(rows, 8)
    return ns

def primitive(v):
    den = 1
    for x in v: den = den * x.denominator // gcd(den, x.denominator)
    w = [int(x*den) for x in v]
    g = 0
    for x in w: g = gcd(g, abs(x))
    return [x//g for x in w]

def run(n, verbose=True):
    ps = primes_of(n); k = len(ps)
    assert all(n % (p*p) for p in ps) and n % 8 in (1,3) and n > 1
    D = -n if n % 4 == 3 else -4*n
    forms = reduced_forms(D)
    h = len(forms)
    wK = 3 if n == 3 else 1
    # ideals of norm prime to 2n in each class
    ideals = []
    for (a,b,c) in forms:
        found = None
        for x in range(0, 60):
            for y in range(-60, 60):
                if gcd(x, abs(y)) != 1: continue
                m = a*x*x + b*x*y + c*y*y
                if m > 0 and gcd(m, 2*n) == 1:
                    found = (x,y,m); break
            if found: break
        x,y,m = found
        g,v,u = egcd(x, y)  # x*v + y*u = 1  -> matrix [[x, -u],[y, v]]
        assert g in (1,-1)
        if g == -1: v, u = -v, -u
        U, V = -u, v           # x*V - U*y = 1
        assert x*V - U*y == 1
        B2 = 2*a*x*U + b*(x*V + U*y) + 2*c*y*V
        assert (B2*B2 - D) % (4*m) == 0
        ideals.append((m, B2))
    tn = {d: tunnell(d) for d in range(1, n+1) if n % d == 0}
    # all admissible tau
    r = isqrt(n); taus = []
    for A in range(-r, r+1):
        for B in range(-r, r+1):
            C2 = n - A*A - B*B
            if C2 < 0: continue
            C = isqrt(C2)
            if C*C != C2: continue
            for Cs in ({C, -C}):
                if n % 8 == 1 and Cs % 4 != 0: continue
                taus.append((A,B,Cs))
    results = set()
    allok = True
    for (A,B,C) in taus:
        tauS = Q(0,A,B,C)
        ns = test_vector(n, tauS)
        if len(ns) != 1:
            print(f"n={n} tau={(A,B,C)}: rank of pi_Z^Un = {len(ns)}  (IsTestVector unsatisfiable / degenerate)")
            allok = False
            continue
        F = primitive(ns[0])
        vals = []
        for (m, B2) in ideals:
            if D % 4 != 0:
                al = qadd(Q(Fr(-B2,2),0,0,0), tuple(t/2 for t in tauS))
            else:
                al = qadd(Q(Fr(-B2,2),0,0,0), tauS)
            assert is_hurwitz(al)
            beta = rgen(Q(m,0,0,0), al)
            assert nrd(beta) == m, (n, m, nrd(beta))
            vals.append(F[cls(qconj(beta))])
        line = []
        for d2 in sorted(tn):
            d1 = n // d2
            T = [q for q in ps if d2 % q == 0]
            P = 0
            for (m, B2), fv in zip(ideals, vals):
                ch = 1
                for q in T: ch *= jacobi(m, q)
                P += ch * fv
            pred = None
            if d2 % 8 == 1:
                num = wK * abs(tn[d1] * tn[d2])
                assert num % 2 == 0, (n, d1, d2, tn[d1], tn[d2])
                pred = num // 2
                ok = abs(P) == pred
            elif d1 % 8 != 1:
                pred = 0; ok = (P == 0)
            else:
                ok = True
            if not ok: allok = False
            line.append((d1, d2, P, pred, ok))
        results.add((tuple(sorted(set(abs(x) for x in F))), tuple((d1,d2,abs(P),pred,ok) for d1,d2,P,pred,ok in line)))
    if verbose:
        print(f"n={n} (mod 8 = {n%8}) k={k} h={h} #tau={len(taus)} Lcal={{" + ", ".join(f"{d}:{abs(tn[d])}/{2**len(primes_of(d))}" for d in sorted(tn)) + "}")
        for fvals, line in sorted(results):
            print("   |f| values", fvals, " (d1,d2,|P|,pred,ok):", [(a,b,c,d,'OK' if e else 'FAIL') for a,b,c,d,e in line])
    return allok

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]]
    bad = []
    for n in ns:
        if not run(n): bad.append(n)
    print("FAILED n:", bad)
