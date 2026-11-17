# Numerical check of Tunnell's formula (Invent. Math. 72 (1983); theorem number UNVERIFIED):
# for odd squarefree n, L(C_n, 1) = beta * (B(n) - A(n)/2)^2 / (4 sqrt n),
# C_n : y^2 = x^3 - n^2 x, beta = int_1^oo dx/sqrt(x^3 - x),
# A(n) = #{(x,y,z) in Z^3 : 2x^2 + y^2 + 8z^2 = n}, B(n) = #{2x^2 + y^2 + 32z^2 = n}.
# Also prints TYZ's lcalSq(n) = L / (2^(2k-3) * (2/sqrt n) * beta) and ((A-2B)/2^(k+1))^2.
import cypari2, math
pari = cypari2.Pari()
pari.set_real_precision(38)
beta = pari('intnum(x=[1,-1/2],[oo,-3/2],1/sqrt(x^3-x))')
def cnt(n, c):
    r = 0
    m = math.isqrt(n)
    for x in range(-m, m+1):
        for y in range(-m, m+1):
            for z in range(-m, m+1):
                if 2*x*x + y*y + c*z*z == n: r += 1
    return r
sample = [1,3,5,7,11,13,15,17,19,21,23,33,35,41,51,57,59,65,73,83,89,97,105,113,123,129,131,155,161,187]
assert len(sample) <= 30
print("beta =", beta)
worst = 0
for n in sample:
    assert pari(f'issquarefree({n})') and n % 2 == 1
    E = pari(f'ellinit([-{n}^2,0])')
    L = pari.lfun(E, 1)
    A, B = cnt(n, 8), cnt(n, 32)
    rhs = beta * (B - A/2)**2 / (4*pari(n).sqrt())
    k = len(pari.factor(n)[0]) if n > 1 else 0
    lcal = L / (pari(2)**(2*k-3) * 2/pari(n).sqrt() * beta)
    tun = pari((A - 2*B))**2 / pari(2)**(2*k+2)
    d = abs(L - rhs)
    worst = max(worst, float(d))
    print(n, n % 8, "A", A, "B", B, "L", pari.precision(L, 10), "rhs", pari.precision(rhs, 10), "diff", float(d),
          "lcalSq", pari.precision(lcal, 10), "((A-2B)/2^(k+1))^2", tun)
print("max |L - rhs| =", worst)
