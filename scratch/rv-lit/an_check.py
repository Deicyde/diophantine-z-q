"""Mathlib's WeierstrassCurve.LFunction recipe (LFunction.lean, Reduction.lean), transcribed, vs PARI ellan.
Per prime p: minimal model (PARI global minimal model is minimal at every p); good iff v_p(Δ)=0,
a_p = p+1-#(affine F_p points + infinity); multiplicative iff v_p(c4)=0: split iff
c4 T^2 + a1 c4 T - (54 b6 - 3 b2 b4 + a2 c4) has a root mod p (Mathlib's criterion), a_p = +1/-1;
additive: a_p = 0. Local factor 1/f_p(p^-s); coefficients multiplied out."""
import cypari2
pari = cypari2.Pari()
N = 300
def primes(n): return [int(p) for p in pari.primes(pari.primepi(n))]
def recipe_an(ainv, N):
    E = pari.ellinit(ainv)
    M = pari.ellminimalmodel(E)
    a1,a2,a3,a4,a6 = [int(x) for x in M[:5]]
    b2,b4,b6 = int(M[5]), int(M[6]), int(M[7])
    c4, D = int(M[9]), int(M[11])
    ap = {}; kind = {}
    for p in primes(N):
        if D % p:
            cnt = 1 + sum(1 for x in range(p) for y in range(p)
                          if (y*y + a1*x*y + a3*y - (x**3 + a2*x*x + a4*x + a6)) % p == 0)
            ap[p] = p + 1 - cnt; kind[p] = 'g'
        elif c4 % p:
            A, B, C = c4 % p, (a1*c4) % p, (-(54*b6 - 3*b2*b4 + a2*c4)) % p
            split = any((A*t*t + B*t + C) % p == 0 for t in range(p))
            ap[p] = 1 if split else -1; kind[p] = 's' if split else 'n'
        else:
            ap[p] = 0; kind[p] = 'a'
    an = [0]*(N+1); an[1] = 1
    # prime power coefficients
    pp = {}
    for p in primes(N):
        c = [1]; k = 1
        while p**k <= N:
            prev2 = c[k-2] if k >= 2 else 0
            c.append(ap[p]*c[k-1] - (p*prev2 if kind[p] == 'g' else 0)); k += 1
        pp[p] = c
    for n in range(2, N+1):
        f = pari.factor(n); v = 1
        for i in range(len(f[0])):
            v *= pp[int(f[0][i])][int(f[1][i])]
        an[n] = v
    return an[1:], kind, E
curves = []
for d in [5, 13, 21, 29, 37, 53, 1, 6, 7, 15, 34]:
    curves.append(('C_%d' % d, [0, 0, 0, -d*d, 0]))
for lab, a in [('11a1',[0,-1,1,-10,-20]),('14a1',[1,0,1,4,-6]),('15a1',[1,1,1,-10,-10]),
               ('17a1',[1,-1,1,-1,-14]),('20a1',[0,1,0,4,4]),('21a1',[1,0,0,-4,-1]),
               ('24a1',[0,-1,0,-4,4]),('26a1',[1,0,1,-5,-8]),('26b1',[1,-1,1,-3,3]),
               ('30a1',[1,0,1,1,2]),('33a1',[1,1,0,-11,0]),('34a1',[1,0,0,-3,1]),
               ('35a1',[0,1,1,9,1]),('37a1',[0,0,1,-1,0]),('nonmin',[0,0,0,-16*64,0]),
               ('y2=x3+x2+... ', [1,1,1,1,1]), ('x3-x+64^3', [0,0,0,-4096,262144]), ('2^6 scaled 11a1', [0,-4,8,-160,-1280])]:
    curves.append((lab, a))
bad = 0
for lab, a in curves:
    an, kind, E = recipe_an(a, N)
    ref = [int(x) for x in pari.ellan(E, N)]
    ok = an == ref
    bad += not ok
    badp = {p: k for p, k in kind.items() if k != 'g'}
    print(lab, a, 'N =', pari.ellglobalred(E)[0], 'bad types', badp, 'MATCH' if ok else 'MISMATCH')
print('curves', len(curves), 'mismatches', bad)
