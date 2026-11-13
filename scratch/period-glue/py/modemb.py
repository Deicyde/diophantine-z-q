"""period-glue: modular embedding of generators of Gamma*.
For x in N_B(O)^+ find u in O^x with y = x*u satisfying y mu ybar = nrd(x) mu (then the lattice map is symplectic),
the integer matrix R (b_k -> y^{-1} b_k x in the basis of O), the symplectic basis change, M in Sp4(Z) with
Omega(g tau) = (A Omega + B)(C Omega + D)^{-1}, and the factor identity
  det(g) * det(C Omega(tau) + D) * (tau-3)(tau+1) = eps * denom(g,tau)^2 * (g tau - 3)(g tau + 1),  eps^4 = 1.
Exact (sympy) for the elliptic generators. Run: ~/pyenv/bin/python -I modemb.py"""
import sympy as sp, itertools
R_ = sp.Rational; s2 = sp.sqrt(2)
def qmul(x, y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y   # i^2=2, j^2=-3, k=ij
    return (a1*a2 + 2*b1*b2 - 3*c1*c2 + 6*d1*d2, a1*b2 + b1*a2 + 3*(c1*d2 - d1*c2),
            a1*c2 + c1*a2 + 2*(b1*d2 - d1*b2), a1*d2 + d1*a2 + b1*c2 - c1*b2)
def nrd(x): a,b,c,d = x; return a*a - 2*b*b + 3*c*c - 6*d*d
def conj(x): a,b,c,d = x; return (a,-b,-c,-d)
def inv(x): n = nrd(x); return tuple(sp.nsimplify(t)/n for t in conj(x))
basis = [(1,0,0,0), (0,1,0,0), (R_(1,2),0,R_(1,2),0), (0,R_(1,2),0,R_(1,2))]
Bm = sp.Matrix([[sp.nsimplify(t) for t in b] for b in basis]).T
def coords(x): return list(Bm.solve(sp.Matrix([sp.nsimplify(t) for t in x])))
def inO(x): return all(sp.nsimplify(t).is_integer for t in coords(x))
mu = (0,0,2,1)
def iota(x):
    x0,x1,x2,x3 = [sp.nsimplify(t) for t in x]
    Mi = sp.Matrix([[s2,0],[0,-s2]]); Mj = sp.Matrix([[0,-3],[1,0]])
    return x0*sp.eye(2) + x1*Mi + x2*Mj + x3*Mi*Mj
# symplectic basis: e = (b0, b1), f = (b2, b3) P^{-1}; as integer combos of b_k:
Pinv = sp.Matrix([[-2,-1],[-1,-1]])
Sbasis = sp.zeros(4,4)   # columns: coordinates (in b_k) of e1,e2,f1,f2
Sbasis[0,0] = 1; Sbasis[1,1] = 1
for c in range(2):
    for r in range(2): Sbasis[2+r, 2+c] = Pinv[r, c]
def form(a, b): return 2*sp.nsimplify(qmul(qmul(inv(mu), a), conj(b))[0])  # Trd(mu^{-1} a bbar)
def vec(cs): return tuple(sum(sp.nsimplify(cs[k])*sp.nsimplify(basis[k][t]) for k in range(4)) for t in range(4))
J = sp.Matrix(4,4, lambda r,c: form(vec(Sbasis[:,r]), vec(Sbasis[:,c])))
print("Gram of symplectic basis:", J.tolist())
# units of O of small size (nrd +-1)
units = []
rng = range(-3,4)
for n in itertools.product(rng, repeat=4):
    x = vec(n)
    if abs(nrd(x)) == 1: units.append(x)
print("small units:", len(units))
tau = sp.symbols('tau')
v = sp.Matrix([tau, 1])
def Omega(t):
    cols = [iota(b)*sp.Matrix([t,1]) for b in basis]
    E = sp.Matrix.hstack(cols[0], cols[1]); F = sp.Matrix.hstack(cols[2], cols[3]) * Pinv
    return F.inv()*E
def analyse(name, x):
    n = nrd(x); found = None
    for u in units:
        y = qmul(x, u)
        if all(sp.simplify(a - n*b) == 0 for a, b in zip(qmul(qmul(y, mu), conj(y)), mu)):
            found = (u, y); break
    if found is None: print(name, "no unit found"); return None
    u, y = found
    yi = inv(y)
    Rb = sp.Matrix(4,4, lambda k,l: coords(qmul(qmul(yi, basis[k]), x))[l])   # b_k -> sum_l R[k,l] b_l
    # new basis vectors (lattice at g tau) in terms of old: w'_k = c * iota(y) * sum_l Rb[k,l] w_l
    # symplectic: S' = Rb^T applied: new symplectic vector j = sum_k Sbasis[k,j] w'_k
    T = Sbasis.inv() * Rb.T * Sbasis   # columns: new symplectic vectors in old symplectic basis
    sympl = sp.simplify(T.T*J*T - J) == sp.zeros(4)
    # period matrix: new basis (E', F') = c iota(y) (E,F) T ; Omega' = F'^{-1} E' ; with blocks of T
    T11, T12, T21, T22 = T[:2,:2], T[:2,2:], T[2:,:2], T[2:,2:]
    # E' = E T11 + F T21, F' = E T12 + F T22  =>  Omega' = (Om T12 + T22)^{-1}(Om T11 + T21) = (T11^T Om + T21^T)(T12^T Om + T22^T)^{-1}
    A, B, C, D = T11.T, T21.T, T12.T, T22.T
    M = sp.Matrix(sp.BlockMatrix([[A, B], [C, D]]))
    g = iota(x); a,b,c,d = g[0,0], g[0,1], g[1,0], g[1,1]
    gt = (a*tau + b)/(c*tau + d)
    Om = Omega(tau); Omg = Omega(gt)
    chk = sp.simplify((A*Om + B) - Omg*(C*Om + D))
    fac = sp.simplify(g.det() * (C*Om + D).det() * (tau-3)*(tau+1) / ((c*tau+d)**2 * (gt-3)*(gt+1)))
    print(f"{name}: x={x} nrd={n} u={u} y={y} symplectic={sympl}")
    print("   M =", M.tolist())
    print("   Omega(g tau) = M.Omega(tau):", chk == sp.zeros(2))
    print("   det g * det(C Om + D) (t-3)(t+1) / (denom^2 (gt-3)(gt+1)) =", fac)
    return M
gens = {"g2 = mu = 2j+ij": (0,0,2,1), "g4 = 1+i+j": (1,1,1,0), "g6 = j(1+j)/2": qmul((0,0,1,0),(R_(1,2),0,R_(1,2),0))}
Ms = {k: analyse(k, x) for k, x in gens.items()}
# triangle relation: products of the generators up to scalars
def is_scalar(x): return all(sp.nsimplify(t) == 0 for t in x[1:])
for p in itertools.permutations(gens.items()):
    (n1,x1),(n2,x2),(n3,x3) = p
    pr = qmul(qmul(x1, x2), x3)
    print("product", n1, "*", n2, "*", n3, "=", pr, "scalar" if is_scalar(pr) else "")
