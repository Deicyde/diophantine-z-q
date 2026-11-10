#!/usr/bin/env python3
"""Independent numerical checks of pd-paper.md section 4 and 5 (own implementation)."""
import math, sys
from math import log, gcd

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]

P = primes_upto(2 * 10**6)
PS = set(P)

# ---- Lemma 4.3: rho(q) = 2q-1 for q = 1 mod 4, q != l, any b with b^2=-1 mod l
def check_43():
    bad = 0
    for l in [5, 13, 17, 29]:
        b = next(x for x in range(1, l) if (x*x + 1) % l == 0)
        for q in [q for q in P if q % 4 == 1 and q != l and q < 120]:
            cnt = sum(1 for U in range(q) for V in range(q) if ((l*U)**2 + (b + l*V)**2) % q == 0)
            if cnt != 2*q - 1: bad += 1
    print("Lemma 4.3 rho(q)=2q-1 failures:", bad)

# ---- Lemma 4.4 remainders, on actual boxes
def check_44():
    worst = 0.0
    for (N, l) in [(10**6, 5), (10**6, 13), (10**7, 29), (10**8, 53)]:
        T = math.isqrt(N); K = T // l
        for b in [x for x in range(1, l) if (x*x + 1) % l == 0]:
            I1 = range(-K, K + 1)
            I2 = [V for V in range(-(T // l) - 2, T // l + 3) if abs(b + l*V) <= T]
            M1, M2 = len(I1), len(I2)
            assert M1 <= 2*T/l + 1 and M2 <= 2*T/l + 1
            for d in [5, 13, 65, 17, 85, 221, 1105]:
                if l in [q for q in (5, 13, 17) if d % q == 0]: continue
                rho = 1; w = 0
                for q in (5, 13, 17):
                    if d % q == 0: rho *= 2*q - 1; w += 1
                # multSum d: count (U,V) in box with d | F; use residues
                cU = {}
                for U in I1: cU[U % d] = cU.get(U % d, 0) + 1
                cV = {}
                for V in I2: cV[V % d] = cV.get(V % d, 0) + 1
                ms = sum(cU.get(u, 0) * cV.get(v, 0) for u in range(d) for v in range(d)
                         if ((l*u)**2 + (b + l*v)**2) % d == 0)
                R = ms - rho / d**2 * M1 * M2
                bound = 2**w * (M1 + M2 + d)
                worst = max(worst, abs(R) / bound)
    print("Lemma 4.4 max |R_d| / (2^w (M1+M2+d)) =", round(worst, 4), "(must be <= 1)")

# ---- arithmetic functions up to W
W = 10**6
def chi4(n): return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)
def spf_table(n):
    spf = list(range(n + 1))
    for i in range(2, int(n**0.5) + 1):
        if spf[i] == i:
            for j in range(i*i, n + 1, i):
                if spf[j] == j: spf[j] = i
    return spf
spf = spf_table(W)
def factor(n):
    f = {}
    while n > 1:
        q = spf[n]; f[q] = f.get(q, 0) + 1; n //= q
    return f
def r_fun(f):
    v = 1
    for q, k in f.items():
        if q == 2: continue
        if q % 4 == 3: v *= 1 if k % 2 == 0 else 0
        else: v *= k + 1
    return v
def h_fun(f):
    v = 1
    for q, k in f.items():
        if q % 4 != 1 or k > 1: return 0
        v *= 2
    return v
def v_fun(f):
    v = 1
    for q, k in f.items():
        if q == 2: continue
        if k % 2: return 0
        v *= 1 if q % 4 == 3 else k + 1
    return v

def check_claims():
    rv = [0]*(W+1); hv = [0]*(W+1); vv = [0]*(W+1)
    for n in range(1, W+1):
        f = factor(n); rv[n] = r_fun(f); hv[n] = h_fun(f); vv[n] = v_fun(f)
    # Claim B pointwise r <= h*v for n < 20000
    Nc = 20000; conv = [0]*(Nc)
    for m in range(1, Nc):
        if vv[m]:
            for l in range(1, (Nc - 1)//m + 1):
                if hv[l]: conv[m*l] += vv[m]*hv[l]
    fail = sum(1 for n in range(1, Nc) if rv[n] > conv[n])
    print("Claim B r<=h*v failures n<2e4:", fail)
    # R(w), S0(w), partial V
    R = 0.0; S0 = 0.0; Vp = 0.0; minA = 1e9; maxratio = 0
    checkpoints = set([3,4,5,10,30,100,10**3,10**4,10**5,10**6] + list(range(3, 2000)))
    for n in range(1, W+1):
        R += rv[n]/n; S0 += hv[n]/n; Vp += vv[n]/n
        if n >= 3 and n in checkpoints:
            minA = min(minA, R - ((2/3)*log(n) - 2))
            maxratio = max(maxratio, R / S0)
    print("Claim A min over checkpoints of R(w)-((2/3)log w-2):", round(minA, 4))
    print("R(1e6)=%.3f S0(1e6)=%.3f Vpartial(1e6)=%.4f max R/S0=%.4f bound 2zeta(2)^4=%.3f"
          % (R, S0, Vp, maxratio, 2*(math.pi**2/6)**4))
    return hv

def check_45(hv):
    # S(w; l) = sum_{l' | P, l' <= w} g(l'), g(q)=(2q-1)/(q-1)^2, exactly (sum over squarefree D numbers)
    worst = 1e9
    for w in [3, 10, 100, 1000, 10**4, 10**5]:
        for l in [5, 13, 101, 997]:
            S = 0.0
            for n in range(1, w + 1):
                if hv[n] and n % l != 0:
                    g = 1.0
                    for q in factor(n): g *= (2*q - 1)/(q - 1)**2
                    S += g
            lb = ((2/3)*log(w) - 2)/25
            worst = min(worst, S - lb)
            if w in (10**5,) : print("  w=%d l=%d S=%.3f lower bound=%.3f" % (w, l, S, lb))
    print("Lemma 4.5 min S - bound:", round(worst, 4))

def check_51():
    ok = True
    for L in [2, 3, 5, 10, 100, 1000, 10**4, 10**5]:
        tail = sum(1.0/q**2 for q in P if q > L) + 1.0/P[-1]  # crude tail add-on
        if tail > 4*log(4)/(L*log(L)): ok = False; print("Lemma 5.1 fail L=", L)
    print("Lemma 5.1 holds on samples:", ok)
    K0 = sum(log(q)/(q*(q-1)) for q in P)
    print("K0 = sum log p/(p(p-1)) ~", round(K0, 5))

def two_sq_odd(p):
    # p = a^2 + b^2, return odd a
    a = 1
    while a*a < p:
        bb = p - a*a; b = math.isqrt(bb)
        if b*b == bb: return a
        a += 2
    return None

def check_bad(N):
    cls = [p for p in P if p <= N and p % 8 == 1 and p % 7 in (3, 5, 6)]
    cs = {p: two_sq_odd(p) for p in cls}
    T = math.isqrt(N); out = []
    for l in [5, 13, 17, 29, 37, 41, 53]:
        if l**4 > N: break
        cnt = sum(1 for p in cls if cs[p] % l == 0 and (p + 1) % l == 0)
        pred = 2*len(cls)/(l - 1)**2
        out.append((l, cnt, round(pred), round(cnt*l*l*log(N)/N, 3),
                    8*N/l**2 + 4*math.sqrt(N)/l))
    print("N=%d class primes=%d" % (N, len(cls)))
    for t in out: print("  l=%d bad=%d pred=%d  bad*l^2 logN/N=%s  Prop4.1 bound=%.0f" % t)
    big = sum(1 for p in cls for l in [0] if False)
    # count bad at some l > N^{1/4}
    cnt = 0
    for p in cls:
        g = gcd(cs[p], p + 1)
        if g > 1:
            # largest prime factor > N^{1/4}?
            m = g; q = 2; bigq = False
            while q*q <= m:
                while m % q == 0:
                    if q**4 > N: bigq = True
                    m //= q
                q += 1
            if m > 1 and m**4 > N: bigq = True
            cnt += bigq
    print("  class primes bad at some l > N^(1/4):", cnt, " bound 20N^(3/4)=", round(20*N**0.75))

def sanity_cp():
    for p in [17, 41]:
        chi = lambda a: 0 if a % p == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)
        phi = sum(chi(x**3 + x) for x in range(p))
        print("p=%d phi_p(1)=%d c_p=%d" % (p, phi, phi//2))

if __name__ == "__main__":
    check_43(); check_44()
    hv = check_claims(); check_45(hv)
    check_51(); sanity_cp()
    check_bad(2 * 10**6)
