"""h29-proof: numerical check of the two fallback leaves (TYZ Theorem 2.1 for all pairs, TYZ Lemma 2.8)
on TYZ's 8-point model (brandt.py / brandt2.py of h29-fix, copied here unchanged).

For squarefree n = 1, 3 (mod 8), an admissible tau and the test vector f_n, and every set T of primes of n,
P_T = sum_{t in Cl_n} chi_T(t) f_n(t), chi_T(t) = prod_{q in T} (N a / q) (a an ideal of class t prime to q).
With d2 = prod T, d1 = n/d2, checks:
 (V) d1, d2 both != 1 (mod 8)  =>  P_T = 0;
 (F) d2 = 1 (mod 8)            =>  |P_T| = 2^{k-1} w_K |L(d1) L(d2)|  (k = #primes of n);
 (S) n = 1 (mod 8)             =>  P_T = P_{T^c}   (Lemma 2.8);
 (C) n = 3 (mod 8)             =>  chi_T = chi_{T^c} on Cl_n (product formula);
 (PQ) sum_T P_T = 2^k Q(n).
"""
import sys
from itertools import product
from math import isqrt
sys.path.insert(0, __import__('os').path.dirname(__file__))
from brandt import cls, ONE
from brandt2 import (pari, tau_choices, test_vector, int_generator, ideal_class_in_X, sqrt_mod, lcal_sq)

def jacobi(a, m):
    return int(pari.kronecker(a, m))

def classes_all(n):
    bnf = pari.bnfinit(pari('y^2+%d' % n), 1)
    cyc = [int(x) for x in bnf.bnf_get_cyc()]
    h = 1
    for x in cyc:
        h *= x
    def clvec(N, r):
        I = pari.idealhnf(bnf, N, pari('y - %d' % r))
        v = pari.bnfisprincipal(bnf, I, 0)
        return tuple(int(x) % m for x, m in zip(v, cyc))
    found = {tuple(0 for _ in cyc): (1, 0)}
    p = 3
    while len(found) < h:
        if all(p % q for q in range(2, isqrt(p) + 1)) and n % p and pow(-n % p, (p-1)//2, p) == 1:
            for k in (1, 2):
                N = p ** k
                for r in sqrt_mod(-n % N, N):
                    v = clvec(N, r)
                    if v not in found:
                        found[v] = (N, r)
        p += 2
    sq = [v for v in found if all(x % 2 == 0 for x, m in zip(v, cyc) if m % 2 == 0)]
    return found, sq, h, cyc

def primes_of(n):
    return [int(p) for p in pari.factor(n)[0]]

def run(ns, ntau=2):
    allok = True
    for n in ns:
        qs = primes_of(n)
        k = len(qs)
        w = 3 if n == 3 else 1
        found, sq, h, cyc = classes_all(n)
        for abc in tau_choices(n)[:ntau]:
            sp = test_vector(n, abc)
            assert len(sp) == 1
            f = int_generator(sp)
            fv = {v: (f[ideal_class_in_X(n, abc, N, r)] if N > 1 else f[cls[ONE]]) for v, (N, r) in found.items()}
            chiq = {v: {q: jacobi(N, q) for q in qs} for v, (N, r) in found.items()}
            Q = sum(fv[v] for v in sq)
            P = {}
            for bits in product((0, 1), repeat=k):
                T = tuple(q for q, b in zip(qs, bits) if b)
                P[T] = sum((1 if all(True for _ in [0]) else 1) *
                           eval_chi(chiq[v], T) * fv[v] for v in found)
            lines = []
            ok = True
            sumP = 0
            for T, PT in P.items():
                d2 = 1
                for q in T:
                    d2 *= q
                d1 = n // d2
                Tc = tuple(q for q in qs if q not in T)
                sumP += PT
                if d1 % 8 != 1 and d2 % 8 != 1:
                    ok &= (PT == 0); tag = "V"
                elif d2 % 8 == 1:
                    l1, l2 = lcal_sq(d1), lcal_sq(d2)
                    ok &= (PT * PT == 4 ** (k - 1) * w * w * l1 * l2); tag = "F(L1^2=%d,L2^2=%d)" % (l1, l2)
                else:
                    tag = "-"
                if n % 8 == 1:
                    ok &= (PT == P[Tc]); tag += ",S"
                else:
                    ok &= all(eval_chi(chiq[v], T) == eval_chi(chiq[v], Tc) for v in found); tag += ",C"
                lines.append("(%d,%d):P=%d[%s]" % (d1, d2, PT, tag))
            ok &= (sumP == 2 ** k * Q)
            allok &= ok
            print("n=%d tau=%s h=%d cyc=%s Q=%d sumP=%d=2^%d*Q? %s | %s | %s"
                  % (n, abc, h, cyc, Q, sumP, k, sumP == 2 ** k * Q, " ".join(lines), "OK" if ok else "FAIL"))
    print("ALL OK" if allok else "SOME FAIL")

def eval_chi(cq, T):
    s = 1
    for q in T:
        s *= cq[q]
    return s

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [11, 17, 33, 35, 41, 51, 57, 73, 105, 113, 123, 145, 195, 219]
    run(ns)
