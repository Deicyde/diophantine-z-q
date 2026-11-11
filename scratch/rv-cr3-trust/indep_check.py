"""rv-cr3-trust: independent recheck of cr3-trust A6 (count 386, Sel2 = 8) and of the D-step premises.
T5bCl from exact class numbers (counting reduced forms; no PARI), genus theory #Cl^2 = h/2^(t-1).
Sample: 30 values (every 13th of the T5bCl=1 list, starting at index 6, so disjoint from cr3-trust's
'every 13th' sample from index 0). For each: dim Sel2 by PARI ell2cover (independent of mirror.py),
root number, conductor == 32 d^2, and a Heegner field D (D = 1 mod 8 fundamental, D < 0, all p | d split)
with analytic rank of the twist C_d^D equal to 0 (L(C_d^D,1) != 0, numerical)."""
import sys, itertools, math
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
from sympy import factorint

def classno(D):  # exact class number of primitive forms of disc D<0
    h = 0; a = 1
    while 3*a*a <= -D:
        for b in range(-a+1, a+1):
            if (b*b - D) % (4*a): continue
            c = (b*b - D)//(4*a)
            if c < a: continue
            if b < 0 and a == c: continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1: continue
            h += 1
        a += 1
    return h

def gCl(m):  # #Cl(Q(sqrt(-m)))^2, m odd squarefree
    D = -m if m % 4 == 3 else -4*m
    t = len(factorint(-D))
    h = classno(D)
    assert h % 2**(t-1) == 0
    return h // 2**(t-1)

def setparts(s):
    if not s: yield []; return
    f, rest = s[0], s[1:]
    for p in setparts(rest):
        for i in range(len(p)):
            yield p[:i] + [[f]+p[i]] + p[i+1:]
        yield [[f]] + p

_g = {}
def T5bCl(ps):
    tot = 0
    for P in setparts(ps):
        cls = [math.prod(B) % 8 for B in P]
        if cls.count(7) != 1 or cls.count(3) != 1 or any(c not in (1, 3, 7) for c in cls): continue
        pr = 1
        for B in P:
            m = math.prod(B)
            if m not in _g: _g[m] = gCl(m)
            pr *= _g[m]
        tot += pr
    return tot % 2

L = []
for d in range(5, 30000, 8):
    f = factorint(d)
    if any(e > 1 for e in f.values()) or not 3 <= len(f) <= 5: continue
    if T5bCl(sorted(f)) == 1: L.append(d)
print("T5bCl=1 count (3..5 primes, d<30000):", len(L), flush=True)
sample = L[6::13][:30]
START = int(sys.argv[1]) if len(sys.argv) > 1 else 0
sample = sample[START:]
HEEGNER = not (len(sys.argv) > 2 and sys.argv[2] == 'noheegner')
print("sample:", sample, flush=True)
bad = 0
for d in sample:
    E = pari.ellinit([0, 0, 0, -d*d, 0])
    sel = len(pari.ell2cover(E))
    rn = int(pari.ellrootno(E)); N = int(pari.ellglobalred(E)[0])
    ps = list(factorint(d))
    D = None
    for k in (range(1, 2000) if HEEGNER else []):
        Dc = 1 - 8*k
        if not pari.isfundamental(Dc): continue
        if any(pari.kronecker(Dc, p) != 1 for p in ps): continue
        ED = pari.ellinit([0, 0, 0, -d*d*Dc*Dc, 0])
        r = int(pari.ellanalyticrank(ED)[0])
        if r == 0:
            D = Dc; break
    ok = sel == 3 and rn == -1 and N == 32*d*d and (D is not None or not HEEGNER)
    bad += not ok
    print(d, ps, "dimSel2=%d rootno=%d N==32d^2:%s HeegnerD=%s" % (sel, rn, N == 32*d*d, D), "OK" if ok else "FAIL", flush=True)
print("failures:", bad)
