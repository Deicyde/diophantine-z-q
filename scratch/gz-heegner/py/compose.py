# Check the Dirichlet-composition lattice identity  J * Q'.lat = Q.lat,  J * Q'.latN = Q.latN
# Elements x + y*s of Q(s), s^2 = D, as pairs of Fractions.
from fractions import Fraction as F
from sympy import Matrix, ilcm
from math import gcd
import itertools, random

def mul(u, v, D):
    return (u[0]*v[0] + u[1]*v[1]*D, u[0]*v[1] + u[1]*v[0])

def hnf_span(vecs):
    # Z-span of rational 2-vectors -> canonical basis (via integer HNF after scaling)
    den = 1
    for v in vecs:
        for c in v: den = ilcm(den, F(c).denominator)
    M = Matrix([[int(F(c)*den) for c in v] for v in vecs])
    from sympy.matrices.normalforms import hermite_normal_form
    H = hermite_normal_form(M.T)  # columns span
    cols = [tuple(F(int(x), den) for x in H.col(j)) for j in range(H.shape[1]) if any(H.col(j))]
    return sorted(cols)

def lat(A, B, D, N=1):
    # <1/N, tau>, tau = (-B + s)/(2A)
    return [(F(1, N), F(0)), (F(-B, 2*A), F(1, 2*A))]

def prodlat(L1, L2, D):
    return [mul(u, v, D) for u in L1 for v in L2]

def crt(r1, m1, r2, m2):
    for x in range(m1*m2):
        if x % m1 == r1 % m1 and x % m2 == r2 % m2: return x
    return None

def test(D, N, A, B, a, b, sign):
    assert (B*B - D) % (4*A) == 0 and (b*b - D) % (4*a) == 0 and A % N == 0
    Bp = crt(B, 2*A, sign*b, 2*a*1) if True else None
    # moduli 2A and 2a share factor 2; both odd residues -> solve mod 2aA
    Bp = None
    for x in range(-2*a*A, 2*a*A):
        if (x - B) % (2*A) == 0 and (x - sign*b) % (2*a) == 0:
            Bp = x; break
    assert Bp is not None and (Bp*Bp - D) % (4*a*A) == 0
    J = [(F(a), F(0)), (F(-b, 2), F(1, 2))]
    ok1 = hnf_span(prodlat(J, lat(a*A, Bp, D), D)) == hnf_span(lat(A, B, D))
    ok2 = hnf_span(prodlat(J, lat(a*A, Bp, D, N), D)) == hnf_span(lat(A, B, D, N))
    return ok1, ok2, Bp

random.seed(1)
res = {1: [], -1: []}
cnt = 0
for D in [-23, -31, -47, -71, -79, -95, -119, -143, -167, -191]:
    for N in [1, 2, 3, 5, 6, 7, 10, 14]:
        for A in range(1, 40):
            if A % N: continue
            for B in range(-A, A+1):
                if (B*B - D) % (4*A) or gcd(gcd(A, B), (B*B-D)//(4*A)) != 1: continue
                for a in range(1, 25):
                    if gcd(a, A) != 1: continue
                    for b in range(-a, a+1):
                        if (b*b - D) % (4*a): continue
                        if cnt > 400: break
                        cnt += 1
                        for sg in (1, -1):
                            o1, o2, _ = test(D, N, A, B, a, b, sg)
                            res[sg].append(o1 and o2)
print({k: (sum(v), len(v)) for k, v in res.items()})
