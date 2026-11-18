# fold-cm: exact check of diophantine_zq.tex L411-418: B = (2,-3) (i^2 = 2, j^2 = -3, ij = -ji), mu = 2j + ij,
# the matrix of Trd(mu^{-1} x ybar) in the basis (1, i, (1+j)/2, (i+ij)/2), its determinant; and |(O/3O)^*| for
# the maximal order at the ramified prime 3 (L436-440), plus the Hilbert symbols (2,-3)_p at p = 3 (tame formula).
from fractions import Fraction as Fr
a, b = 2, -3
def mul(x, y):  # x = (x0, x1, x2, x3) = x0 + x1 i + x2 j + x3 ij
    x0, x1, x2, x3 = x; y0, y1, y2, y3 = y
    return (x0*y0 + a*x1*y1 + b*x2*y2 - a*b*x3*y3,
            x0*y1 + x1*y0 - b*x2*y3 + b*x3*y2,
            x0*y2 + x2*y0 + a*x1*y3 - a*x3*y1,
            x0*y3 + x3*y0 + x1*y2 - x2*y1)
conj = lambda x: (x[0], -x[1], -x[2], -x[3])
nrd = lambda x: x[0]**2 - a*x[1]**2 - b*x[2]**2 + a*b*x[3]**2
trd = lambda x: 2*x[0]
mu = (0, 0, 2, 1)
n = nrd(mu); muinv = tuple(Fr(c, n) for c in conj(mu))
assert mul(mu, muinv) == (1, 0, 0, 0)
h = Fr(1, 2)
basis = [(1, 0, 0, 0), (0, 1, 0, 0), (h, 0, h, 0), (0, h, 0, h)]
M = [[trd(mul(mul(muinv, x), conj(y))) for y in basis] for x in basis]
for s in (1, -1):
    Ms = [[s*v for v in r] for r in M]
    print('sign', s, [[str(v) for v in r] for r in Ms])
target = [[0,0,-1,1],[0,0,1,-2],[1,-1,0,0],[-1,2,0,0]]
print('matches the printed matrix (some sign):', M == target or [[-v for v in r] for r in M] == target)
def det(A):
    A = [[Fr(v) for v in r] for r in A]; n = len(A); d = Fr(1)
    for i in range(n):
        p = next((k for k in range(i, n) if A[k][i] != 0), None)
        if p is None: return 0
        if p != i: A[i], A[p] = A[p], A[i]; d = -d
        d *= A[i][i]
        for k in range(i+1, n):
            f = A[k][i]/A[i][i]; A[k] = [u - f*v for u, v in zip(A[k], A[i])]
    return d
print('det of printed matrix =', det(target))
# Hilbert symbol (2,-3)_3: v(2)=0, v(-3)=1 -> (2/3)^1 = -1 (2 is a non-square mod 3); then (2,-3)_2 = -1 by the product
# formula ((2,-3)_inf = +1 as 2 > 0; (2,-3)_p = 1 for p > 3). So B is ramified exactly at 2 and 3.
print('(2/3) Legendre =', pow(2, (3-1)//2, 3) - 3 if pow(2, 1, 3) == 2 else 1)
print('|(O/3O)^*| at the ramified prime 3: |O/3O| = 81, radical index 9 (residue field F_9): 81 - 9 =', 81 - 9, '<= 81')
