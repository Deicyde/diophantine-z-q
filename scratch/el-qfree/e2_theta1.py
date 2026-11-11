"""E2: exact test of theta in {+-1} (trivial torsion witness) for multipliers m = m0 k^2,
m0 a signed squarefree product of primes <= 324, 1 <= k <= KMAX, on real Test-site pole inputs
B = N/D^2 built with the Lean formulas (k0.py), kappa = 1.
B = N/D reduced (D need not be a square when q is free). theta = +-1 <=> eps*m0*D*(m0 k^2 D - N) is a square;
m0 runs over signed subsets of S cap (supp N cup odd-supp D).
Also reports small prime factors (325..10^5) of D and N."""
import sys, math, itertools
from fractions import Fraction as Fr
import k0
sys.set_int_max_str_digits(0)
from sympy import primerange
SP = list(primerange(2, 325))
KMAX = 256
BIGP = list(primerange(325, 100000))

def vp(x, p):
    e = 0
    while x % p == 0: x //= p; e += 1
    return e

_mods = [(m, set((i*i) % m for i in range(m))) for m in (64, 63, 65, 11, 17, 19, 23, 29, 31, 37)]
def issq(x):
    if x < 0: return False
    for m, r in _mods:
        if x % m not in r: return False
    return math.isqrt(x)**2 == x

def run(n, h, s0, eta, q):
    C = k0.testC(n, 1, Fr(n), h, s0)
    B = k0.testB(n, 1, eta, q, h, s0, C)
    if B is None: return None
    N, Dd = B.numerator, B.denominator
    Dr = Dd
    Sdiv = [p for p in SP if N % p == 0 or (Dd % p == 0 and (lambda e: e % 2 == 1)(vp(Dd, p)))]
    hits = []
    for r in range(len(Sdiv)+1):
        for sub in itertools.combinations(Sdiv, r):
            mabs = math.prod(sub)
            for sg in (1, -1):
                m0 = sg*mabs
                for k in range(1, KMAX+1):
                    v = m0*Dd*(m0*k*k*Dd - N)
                    if issq(v): hits.append((m0, k, +1))
                    if issq(-v): hits.append((m0, k, -1))
    smallD = [p for p in BIGP if Dr % p == 0]
    return dict(Ndig=len(str(abs(N))), Ddig=len(str(Dr)), S_in_N=Sdiv, D_bigp=smallD[:6], Dsq=(math.isqrt(Dd)**2==Dd), hits=hits)

INPUTS = []
for n in (1, 2, 3):
    for (h, s0) in ((2, 2*n), (3, 2*n), (-1, n)):
        for eta in (1, -1):
            for q in (Fr(0), Fr(1, 2)):
                INPUTS.append((n, h, s0, eta, q))
INPUTS = INPUTS[:30]
if __name__ == "__main__":
    for inp in INPUTS:
        r = run(*inp)
        print(inp, r, flush=True)
