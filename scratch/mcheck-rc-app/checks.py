"""mcheck-rc-app: arithmetic spot checks for Appendices E-G of diophantine_zq.tex.
Pure Python (no sympy). Each check prints PASS/FAIL with the tex lines it refers to."""
import math, random, itertools, cmath
random.seed(17)
results = []
def report(name, ok, info=""):
    results.append(ok)
    print(("PASS" if ok else "FAIL"), name, info)

def v2(n):
    n = abs(n); c = 0
    if n == 0: return math.inf
    while n % 2 == 0: n //= 2; c += 1
    return c

def leg(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1

def primes(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
P = primes(3000)

def sqfree(n):
    return all(n % (p*p) for p in P if p*p <= n)

# 1. (K5)-(K6), L6929-6941: v2(s_F) = 2e
ok = True
for _ in range(300):
    e = random.randint(3, 12); Nodd = random.choice([1,3,5,7,11,15,33]); F = random.choice([1,13,17*19,23*29*31])
    c = 1 + 2**e*3*Nodd*F
    sF = (c*c-c)**2
    ok &= (v2(sF) == 2*e)
report("(K6) v2 s_F = 2e", ok)

# 2. L7445-7458: u=1+zeta+zeta^-1, #negative conjugates odd and equals the printed formula
ok = True
for m in range(3, 16):
    neg = sum(1 for a in range(1, 2**(m-1), 2) if 1+2*math.cos(2*math.pi*a/2**m) < 0)
    formula = 2**(m-2) - math.floor(2**(m-1)/3 + 0.5)
    ok &= (neg == formula and neg % 2 == 1)
report("L7445-7458 negative conjugates of 1+zeta+zeta^-1: odd, = printed formula (m=3..15)", ok)

# helper: point count of y^2 = x(x-l)(x+3l) twisted by h, over F_q
def count(l, h, q):
    # E^h: h y^2 = x(x-l)(x+3l)
    cnt = 1
    for x in range(q):
        f = x*(x-l)*(x+3*l) % q
        cnt += 1 + leg(h*f, q) if f else 1
    return cnt
ls = [l for l in range(11, 400, 12) if sqfree(l)]
# 3. L7197-7201: E_q(chi) at t=0 times q = #E^h(F_q)
ok = True
for _ in range(150):
    l = random.choice(ls); q = random.choice([p for p in P[3:120] if l % p]); h = random.choice([-7,-3,5,13,-11,17*3,-23])
    if h % q == 0: continue
    aq = q + 1 - count(l, 1, q)
    ok &= (q + 1 - aq*leg(h, q) == count(l, h, q))
report("L7197-7201 q*E_q(chi_h)(0) = #E^h(F_q)", ok)

# 4. (E.12) closed form / L8131-8180 and mod-8 coefficient L10444-10470 (integer-valued model, eta=psi=1 phases removed)
def coeffs_shell(ap, p, kappa, smax):
    b = [1, ap - kappa]
    for s in range(1, smax): b.append(ap*b[s] - p*b[s-1])
    return b
ok = True
for _ in range(2000):
    p = random.choice(P[2:200]); ap = random.randint(-int(2*p**0.5), int(2*p**0.5))
    eta = random.choice([1, -1]); chi = random.choice([1, -1])  # psi/eta value at p
    for Dsym in (-1, 0, 1):
        kappa = chi*Dsym
        # direct recurrence a(p^2 n) = {eta ap - psi (-n/p)} a(n) - p eta^2 a(n/p^2), n = D p^{2r}
        a = {0: 1}
        psi = chi*eta
        a[1] = (eta*ap - psi*Dsym)*a[0]
        for r in range(1, 6):
            a[r+1] = eta*ap*a[r] - p*eta**2*a[r-1]
        b = coeffs_shell(ap, p, kappa, 6)
        ok &= all(a[r] == eta**r*b[r] for r in range(6))
report("(E.12)/(O.6) closed form a(D p^{2r}) = eta(p)^r A_{p,r}(D)", ok)

ok = True
for _ in range(3000):
    p = random.choice([p for p in P[2:300]]); ap = random.randint(-int(2*p**0.5), int(2*p**0.5))
    eta = random.choice([1, -1])
    a1 = 1; ap2 = eta*(ap - 1); ap4 = eta*ap*ap2 - p*eta**2*a1
    ok &= (ap4 == eta**2*(ap*(ap-1) - p))
    Bp = (ap2 - eta*a1); Bp3 = (ap4 - eta*ap2)        # times 2 (depth zero, n_U = 1)
    ok &= (Bp == eta*(ap-2)) and (Bp3 == eta**2*((ap-1)**2 - p))
    # H[p^3] = (B[p^3] - b_p * Theta_p[p^3])/2, Theta_p[p^3] = eta(p) p
    H4 = Bp3 - Bp*eta*p    # = 4 H[p^3]
    ok &= (H4 == eta**2*(ap-1)*(ap-p-1))
report("L10444-10470 a(p^2), a(p^4), B[p], B[p^3], H[p^3] = eta^2 (a_p-1)(a_p-p-1)/4", ok)
ok = True
for _ in range(3000):
    p = random.choice(P[2:300]); ap = random.randint(-int(2*p**0.5), int(2*p**0.5)); eta=random.choice([1,-1])
    # H[p^2 p'] = (a(p^3 p') - eta a(pp'))/4 with a(p^2 * pp') = eta*ap*a(pp') (kappa = 0)
    app = random.randint(-50, 50)*8
    ok &= ((eta*ap*app - eta*app) == eta*(ap-1)*app)
report("L10411-10416 H[p^2 p'] = eta(p)(a_p-1)a(pp')/4", ok)

# 5. (O.10) shell parity L9600-9625
ok = True
for _ in range(3000):
    p = random.choice(P[2:300]);
    ap = random.choice([x for x in range(-int(2*p**0.5), int(2*p**0.5)+1) if (x - p - 1) % 4 == 0])
    for kappa in (0, 1, -1):
        b = coeffs_shell(ap, p, kappa, 12); bm = [0] + b
        if kappa == 0:
            ok &= all((b[s] - bm[s]) % 2 == 1 for s in range(12))
        else:
            ok &= all(x % 2 == 1 for x in b)
            ok &= all((b[s+1]-b[s]) % 4 == (ap - kappa - 1) % 4 for s in range(11))
report("(O.10) shell parities and d_s == a_p - kappa - 1 mod 4", ok)

# 6. c_0 = |GL_4(F_3)| L8414, L8576
c0 = 1
for i in range(4): c0 *= 3**4 - 3**i
report("c_0 = |GL_4(F_3)| = 24261120, v2 = 9", c0 == 24261120 and v2(c0) == 9, str(c0))
# finite subgroups of GL_4(Z): orders of elements of finite order in GL_4(Z) divide... check max finite group
# orders known to divide c0: e.g. |W(F4)| = 1152, |W(B4)| = 384, |W(A4)xC2| = 240 ; unit groups of Eichler orders have order <= 24
report("abs(R_z^x) in {2,4,6,8,12,24} divide c_0", all(c0 % n == 0 for n in (2,4,6,8,12,24,1152)))

# 7. alpha(-1) = 1 bookkeeping L8578-8590: for m == 3 mod 4 squarefree, prod_{p|m} (-1/p) = -1 ; (-1/l0) = -1 for l0 == -1 mod 4
ok = True
for m in range(3, 3000, 4):
    if not sqfree(m): continue
    pr = 1
    for p in P:
        if p > m: break
        if m % p == 0: pr *= (-1)**((p-1)//2)
    ok &= (pr == -1)
report("prod_{p|m} (-1/p) = -1 for squarefree m == 3 mod 4", ok)

# 8. (O.12) and trace identity L9718-9724, L9869-9883
ok = True
for _ in range(500):
    a,b,c,e,lam,mu = [complex(random.gauss(0,1), random.gauss(0,1)) for _ in range(6)]
    def mm(X,Y): return [[X[0][0]*Y[0][0]+X[0][1]*Y[1][0], X[0][0]*Y[0][1]+X[0][1]*Y[1][1]],[X[1][0]*Y[0][0]+X[1][1]*Y[1][0], X[1][0]*Y[0][1]+X[1][1]*Y[1][1]]]
    tr = lambda X: X[0][0]+X[1][1]
    g=[[a,b],[c,e]]; tau=[[1,0],[0,-1]]; phi=[[lam,0],[0,mu]]
    lhs = lam*(tr(mm(mm(g,tau),phi)) - tr(mm(g,phi))); rhs = lam*mu*(tr(mm(g,tau)) - tr(g))
    ok &= abs(lhs-rhs) < 1e-9
    A=[[a,b],[c,e]]; B=[[lam,b*e],[mu+1,c]]
    detB = B[0][0]*B[1][1]-B[0][1]*B[1][0]
    Binv = [[B[1][1]/detB, -B[0][1]/detB],[-B[1][0]/detB, B[0][0]/detB]]
    ok &= abs(tr(A)*tr(B) - tr(mm(A,B)) - detB*tr(mm(A,Binv))) < 1e-8
report("(O.12) and tr A tr B = tr AB + det B tr AB^-1", ok)

# 9. (O.6) from the H-recurrence L9060-9085, with roots of unity
ok = True
for _ in range(500):
    s = cmath.exp(2j*math.pi*random.randint(0,15)/16); chi = random.choice([1,-1]); mp = random.choice([1,-1]); nsym = random.choice([-1,0,1])
    ap = random.randint(-20,20); p = random.choice(P[2:50]); Hn = complex(random.random(), random.random()); Hn2 = complex(random.random(), random.random())
    # H(p^2 m n) from H-recurrence at index mn: (-mn/p) = mp*nsym
    Hp2 = s*chi*ap*Hn - s*(mp*nsym)*Hn - p*s**2*Hn2
    eta = s*chi; psi = s*mp
    ok &= abs(Hp2 - ((eta*ap - psi*nsym)*Hn - p*eta**2*Hn2)) < 1e-9
report("(O.6) follows from the H-recurrence with eta = s chi, psi = s (m/p)", ok)

# 10. network linear algebra over F_2, L10680-10730
def det2(M):
    M = [r[:] for r in M]; n = len(M); d = 1
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i]), None)
        if piv is None: return 0
        M[i], M[piv] = M[piv], M[i]
        for r in range(i+1, n):
            if M[r][i]: M[r] = [(x+y) % 2 for x, y in zip(M[r], M[i])]
    return 1
def inv2(M):
    n = len(M); A = [M[i][:] + [int(i==j) for j in range(n)] for i in range(n)]
    for i in range(n):
        piv = next((r for r in range(i, n) if A[r][i]), None)
        if piv is None: return None
        A[i], A[piv] = A[piv], A[i]
        for r in range(n):
            if r != i and A[r][i]: A[r] = [(x+y) % 2 for x, y in zip(A[r], A[i])]
    return [row[n:] for row in A]
def kernel2(M):
    n = len(M[0]); ker = []
    for v in itertools.product([0,1], repeat=n):
        if any(v) and all(sum(M[i][j]*v[j] for j in range(n)) % 2 == 0 for i in range(len(M))): ker.append(v)
    return ker
ok = True
for b in range(2, 7):
    T = [[int(i==j or j==(i+1) % b) for j in range(b)] for i in range(b)]   # I + cyclic shift
    for J in itertools.chain.from_iterable(itertools.combinations(range(b), k) for k in range(1, b)):
        TJ = [[T[i][j] for j in J] for i in J]
        ok &= det2(TJ) == 1
    Bm = [[int(i==j==b-1) for j in range(b)] for i in range(b)]
    H = [[0]*b + T[i] for i in range(b)] + [[T[j][i] for j in range(b)] + Bm[i] for i in range(b)]
    ker = kernel2(H)
    ok &= (ker == [tuple([1]*b + [0]*b)])
    # varying network: T = I + lower shift; (T_J^{-1})_{b,1} = 1 iff J = all
    L = [[int(i==j or i==j+1) for j in range(b)] for i in range(b)]
    for J in itertools.chain.from_iterable(itertools.combinations(range(b), k) for k in range(1, b+1)):
        LJ = [[L[i][j] for j in J] for i in J]; Li = inv2(LJ)
        ok &= Li is not None
        ent = Li[J.index(b-1)][J.index(0)] if (0 in J and b-1 in J) else 0
        ok &= (ent == (1 if len(J) == b else 0))
report("network matrices over F_2 (b=2..6): singular T_J invertible on proper J, ker H = <sum u_i>; varying entry (T_J^-1)_{b1}=1 iff J full", ok)

# 11. L10479-10495: 2-primary part of E_l(F_p) has order 4 when p==1 mod 4, (l/p)=-1 (re-check of mcheck-rc-map)
ok = True; n = 0
for l in ls[:20]:
    for p in P[2:200]:
        if p % 4 != 1 or leg(l, p) != -1: continue
        N = count(l, 1, p); n += 1
        ok &= (v2(N) == 2)
report("v2 #E_l(F_p) = 2 for p == 1 mod 4, (l/p) = -1", ok, f"({n} pairs)")

# 12. root-number signs L10046-10049 and L10027-10029 (bookkeeping)
# w(E^{hk0}) = w(E^h) chi_{k0}(-N): k0<0 square at all p | N  => chi_{k0}(-N) = chi_{k0}(-1) = -1 ; w(E^h) = -1 => +1
report("w(E^{h k0}) = (-1)(-1) = +1", (-1)*(-1) == 1)

print(f"{sum(results)}/{len(results)} PASS")
