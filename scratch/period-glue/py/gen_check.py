"""period-glue: numerical check of GammaStarGen. Every x in N(O)^+ (searched independently: x in O with
nrd(x) in {1,2,3,6}, normalizing O, small coordinates; the first 30 in lexicographic order) should be a rational multiple of a word in
x4 = 1+i+j and x6 = (j-3)/2. Greedy reduction: multiply by x4^{+-1}, x6^{+-1}, x2 = 2 x6 x4^{-1} (and
powers, i.e. the vertex stabilizers) to decrease cosh d(g p, p) for a base point p inside the
fundamental triangle; success if the result is a scalar.
Run: ~/pyenv/bin/python -I gen_check.py"""
import itertools, mpmath as mp
from fractions import Fraction as Fr
mp.mp.dps = 30
def qmul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    return (a1*a2 + 2*b1*b2 - 3*c1*c2 + 6*d1*d2, a1*b2 + b1*a2 + 3*(c1*d2 - d1*c2),
            a1*c2 + c1*a2 + 2*(b1*d2 - d1*b2), a1*d2 + d1*a2 + b1*c2 - c1*b2)
def nrd(x): a,b,c,d = x; return a*a - 2*b*b + 3*c*c - 6*d*d
def conj(x): a,b,c,d = x; return (a,-b,-c,-d)
def inv(x): n = nrd(x); return tuple(Fr(t)/n for t in conj(x))
basis = [(Fr(1),0,0,0), (0,Fr(1),0,0), (Fr(1,2),0,Fr(1,2),0), (0,Fr(1,2),0,Fr(1,2))]
def vec(n): return tuple(sum(Fr(n[k])*Fr(basis[k][t]) for k in range(4)) for t in range(4))
def coords(x):  # solve x = sum n_k b_k
    a,b,c,d = x; n2 = 2*c; n3 = 2*d; n0 = a - c; n1 = b - d
    return (n0, n1, n2, n3)
def inO(x): return all(Fr(t).denominator == 1 for t in coords(x))
def normalizes(x):
    xi = inv(x)
    return all(inO(qmul(qmul(x, b), xi)) and inO(qmul(qmul(xi, b), x)) for b in basis)
s2 = mp.sqrt(2)
def mob(x):
    a,b,c,d = [mp.mpf(Fr(t).numerator)/Fr(t).denominator for t in x]
    return (a + b*s2, -3*c - 3*s2*d, c - s2*d, a - b*s2)
def act(x, z):
    A,B,C,D = mob(x); return (A*z + B)/(C*z + D)
def coshd(z, w): return 1 + abs(z - w)**2/(2*z.imag*w.imag)
x4 = (Fr(1),Fr(1),Fr(1),Fr(0)); x6 = (Fr(-3,2),Fr(0),Fr(1,2),Fr(0))
x2 = qmul(tuple(2*t for t in x6), inv(x4))
p4 = mp.sqrt(2) + 1j; p6 = mp.sqrt(3)*1j
def fixpt(x):
    A,B,C,D = mob(x); disc = (A+D)**2 - 4*(A*D - B*C)
    z = ((A-D) + mp.sqrt(disc))/(2*C)
    return z if mp.im(z) > 0 else ((A-D) - mp.sqrt(disc))/(2*C)
p2 = fixpt(x2)
p = (p4 + p6 + p2)/3   # base point inside the triangle
gens = []
for g, k in ((x4, 4), (x6, 6), (x2, 2)):
    y = g
    for e in range(1, k):
        gens.append(y); gens.append(inv(y)); y = qmul(y, g)
def is_scalar(x): return x[1] == 0 and x[2] == 0 and x[3] == 0
def reduce(x, maxit=200):
    word = 0
    for _ in range(maxit):
        if is_scalar(x): return True, word
        cur = coshd(act(x, p), p)
        best = None
        for g in gens:
            y = qmul(g, x); v = coshd(act(y, p), p)
            if v < cur - mp.mpf('1e-12') and (best is None or v < best[0]): best = (v, y)
        if best is None: return False, word
        x = best[1]; word += 1
    return False, word
found = 0; ok = 0; fails = []
R = range(-4, 5)
for n in itertools.product(R, repeat=4):
    if found >= 30: break   # sample of at most 30 inputs (task resource rule)
    x = vec(n)
    N = nrd(x)
    if N not in (1, 2, 3, 6) or not normalizes(x): continue
    found += 1
    r, w = reduce(x)
    ok += r
    if not r: fails.append((n, N))
print("sample: first 30 elements of N(O)^+ with |coords| <= 4 in N5's basis, nrd in {1,2,3,6}:", found)
print("reduced to a scalar by greedy reduction in <x4, x6>:", ok)
print("failures (first 10):", fails[:10])
