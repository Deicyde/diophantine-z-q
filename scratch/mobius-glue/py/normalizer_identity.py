# Coordinates of O = Z<1, i, (1+j)/2, (i+k)/2> in B = (2,-3)_Q, product mulCoord copied from
# ZInQKernel/HDecomp/QM/Structures.lean. Computes the quadratic forms c_{k,l}(x) = coord_l(x e_k xbar)
# and the Smith normal form of their coefficient matrix on the 10 monomials x_i x_j.
import sympy as sp
x = sp.symbols('x0:4')
def mulCoord(n, m):
    return [m[0]*n[0] + 2*m[1]*n[1] + 2*m[1]*n[3] - m[2]*n[2] + 2*m[3]*n[3],
            m[0]*n[1] + m[1]*n[0] + m[1]*n[2] - m[2]*n[3] + m[3]*n[2],
            m[0]*n[2] - 2*m[1]*n[3] + m[2]*n[0] + m[2]*n[2] + 2*m[3]*n[1],
            m[0]*n[3] - m[1]*n[2] + m[2]*n[1] + m[2]*n[3] + m[3]*n[0]]
# ofInt n = n0 + n1 i + n2 (1+j)/2 + n3 (i+k)/2 ; quaternion coords re, imI, imJ, imK
def toQ(n): return [n[0]+sp.Rational(1,2)*n[2], n[1]+sp.Rational(1,2)*n[3], sp.Rational(1,2)*n[2], sp.Rational(1,2)*n[3]]
def fromQ(q):  # inverse
    n2 = 2*q[2]; n3 = 2*q[3]; return [sp.expand(q[0]-q[2]), sp.expand(q[1]-q[3]), sp.expand(n2), sp.expand(n3)]
def qmul(a, b):  # (2,-3): i^2=2, j^2=-3, k=ij, k^2 = -c1 c2 = 6
    c1, c2 = 2, -3
    a0,a1,a2,a3 = a; b0,b1,b2,b3 = b
    return [a0*b0 + c1*a1*b1 + c2*a2*b2 - c1*c2*a3*b3,
            a0*b1 + a1*b0 - c2*a2*b3 + c2*a3*b2,
            a0*b2 + c1*a1*b3 + a2*b0 - c1*a3*b1,
            a0*b3 + a1*b2 - a2*b1 + a3*b0]
# check mulCoord against qmul on symbols
y = sp.symbols('y0:4')
lhs = [sp.expand(t) for t in toQ(mulCoord(list(x), list(y)))]
rhs = [sp.expand(t) for t in qmul(toQ(list(x)), toQ(list(y)))]
print('mulCoord check (n*m order?):', [sp.simplify(a-b) for a,b in zip(lhs,rhs)])
rhs2 = [sp.expand(t) for t in qmul(toQ(list(y)), toQ(list(x)))]
print('reverse order check:', [sp.simplify(a-b) for a,b in zip(lhs,rhs2)])
q = toQ(list(x))
nrd = sp.expand(q[0]**2 - 2*q[1]**2 + 3*q[2]**2 - 6*q[3]**2)
print('nrd =', nrd)
qbar = [q[0], -q[1], -q[2], -q[3]]
print('conj coords =', fromQ(qbar))
E = [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]
forms = []
for e in E:
    prod = qmul(qmul(q, toQ(e)), qbar)
    forms += [sp.expand(t) for t in fromQ(prod)]
mons = [x[i]*x[j] for i in range(4) for j in range(i,4)]
M = sp.Matrix([[sp.Poly(f, *x).coeff_monomial(m) for m in mons] for f in forms])
print('all integer:', all(c.is_integer for c in M))
from sympy.matrices.normalforms import smith_normal_form
print('rank', M.rank())
print('SNF diag', [smith_normal_form(M, domain=sp.ZZ)[i,i] for i in range(10)])

# integer coefficients lam with sum_r lam_r * forms[r] = 6 * x_i^2 (PARI matsolvemod over Z)
import cypari2
pari = cypari2.Pari()
Mt = M.T  # 10 x 16
rows = '[' + ';'.join(','.join(str(Mt[a,b]) for b in range(16)) for a in range(10)) + ']'
sols = []
for i in range(4):
    target = [0]*10
    target[mons.index(x[i]**2)] = 6
    col = '[' + ','.join(str(t) for t in target) + ']~'
    sol = pari(f'matsolvemod({rows}, 0, {col})')
    lam = [int(sol[r]) for r in range(16)]
    chk = sp.expand(sum(l*f for l, f in zip(lam, forms)) - 6*x[i]**2)
    print('i =', i, 'lam =', lam, 'check:', chk)
    sols.append(lam)
# mod-2 and mod-3 checks: x*i in 2O when 2 | nrd(x); x*j in 3O when 3 | nrd(x)
import itertools
nrdf = sp.lambdify(x, nrd)
ok2 = all(all(c % 2 == 0 for c in mulCoord(list(n), [0,1,0,0])) for n in itertools.product(range(2), repeat=4) if nrdf(*n) % 2 == 0)
ok3 = all(all(c % 3 == 0 for c in mulCoord(list(n), [-1,0,2,0])) for n in itertools.product(range(3), repeat=4) if nrdf(*n) % 3 == 0)
print('x*i in 2O when 2|nrd:', ok2, '; x*j in 3O when 3|nrd:', ok3)
print('x*i coords:', [sp.expand(t) for t in mulCoord(list(x), [0,1,0,0])])
print('x*j coords:', [sp.expand(t) for t in mulCoord(list(x), [-1,0,2,0])])
print('forms (k-major, l-minor):')
for r, f in enumerate(forms): print(r, f)
