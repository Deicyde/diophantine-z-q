# Check: E(γ) = phi(a,4b,c/4,d) + phi(a,8b,c/8,d) ≡ 0 mod 12 for γ ∈ Γ0(32);
# phi = etaSqExp (Lean def in Contrib/GZTheta/Eta.lean), Python floor-division semantics = Int.ediv for c>0;
# Lean Int.ediv/emod: a % c in [0,|c|), a/c = (a - a%c)/c.
import random, math, cmath
def ediv(a,c):
    r = a % abs(c)
    return (a - r)//c
def emod(a,c): return a % abs(c)
def phi(a,b,c,d):
    if c == 0: return b if a == 1 else 6 - b
    q = ediv(a,c); r = emod(a,c)
    return q - 3 + phi(c, d, -r, -(b - q*d))
def eta(z, N=200):
    q = cmath.exp(2j*cmath.pi*z)
    p = cmath.exp(2j*cmath.pi*z/24)
    for n in range(1,N): p *= (1-q**n)
    return p
# numeric check of the eta^2 law on a few matrices
random.seed(1)
def rand_sl2(N=1):
    while True:
        c = N*random.randint(-6,6); d = random.randint(-30,30)
        if math.gcd(c,d) != 1: continue
        # solve a d - b c = 1
        g, x, y = egcd(d, -c)  # x*d + y*(-c) = 1
        if g != 1: continue
        a, b = x, y
        k = random.randint(-3,3); a += k*c; b += k*d
        return a,b,c,d
def egcd(a,b):
    if b == 0: return (a,1,0) if a>0 else (-a,-1,0)
    g,x,y = egcd(b, a % b)
    return g, y, x - (a//b)*y
z = 0.123+0.9j
bad = 0
for _ in range(10):
    a,b,c,d = rand_sl2()
    w = (a*z+b)/(c*z+d)
    lhs = eta(w)**2; rhs = cmath.exp(1j*cmath.pi*phi(a,b,c,d)/6)*(c*z+d)*eta(z)**2
    if abs(lhs-rhs) > 1e-6*abs(rhs): bad += 1; print("eta law fails", a,b,c,d, lhs, rhs)
print("eta law numeric failures:", bad)
cnt = {}
for _ in range(3000):
    a,b,c,d = rand_sl2(32)
    E = phi(a,4*b,c//4,d) + phi(a,8*b,c//8,d)
    cnt[E % 12] = cnt.get(E % 12, 0) + 1
print("E mod 12 distribution over Gamma0(32):", cnt)
print("recheck with Im w not tiny")
bad=0; tot=0
for _ in range(400):
    a,b,c,d = rand_sl2()
    z = 0.31+1.7j/max(1,abs(c))
    w = (a*z+b)/(c*z+d)
    if w.imag < 0.05: continue
    tot+=1
    lhs = eta(w,4000)**2; rhs = cmath.exp(1j*cmath.pi*phi(a,b,c,d)/6)*(c*z+d)*eta(z,4000)**2
    if abs(lhs-rhs) > 1e-6*abs(rhs): bad += 1
print("tested", tot, "failures", bad)
