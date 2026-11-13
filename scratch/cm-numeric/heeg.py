"""Shared helpers: Heegner points on X0(32) = A : y^2 = x^3 + 4x via x0-32's eta quotients
(ZInQKernel/Contrib/TYZGenus/X0.lean: xC, yC).  PARI via cypari2."""
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**9, silent=True) if hasattr(pari, 'allocatemem') else None
PREC = 400
pari.set_real_precision(PREC)

def eta(z):
    return pari.eta(z, 1)          # true Dedekind eta (with q^(1/24))

def xy(tau):
    e = {d: eta(d*tau) for d in (2, 4, 8, 16, 32)}
    x = e[2]**2*e[16]/(e[4]*e[32]**2) + 2
    y = -(e[8]**4*e[16]**2/(e[4]**2*e[32]**4))
    return x, y

def tau_of(A, B, D):
    return pari(f"(-({B})+I*sqrt({-D}))/(2*({A}))")

def on_curve(x, y):
    return abs(y**2 - x**3 - 4*x)

def reduce_form(a, b, c):
    """Gauss reduction of a positive definite form; returns reduced (a,b,c)."""
    while True:
        if c < a:
            a, b, c = c, -b, a
            continue
        if b > a or b <= -a:
            # translate b into (-a, a]
            k = (a - b)//(2*a)
            b2 = b + 2*a*k
            c = (b2*b2 - (b*b - 4*a*c))//(4*a)
            b = b2
            continue
        if a == c and b < 0:
            b = -b
            continue
        return (a, b, c)

def gcd3(a, b, c):
    from math import gcd
    return gcd(gcd(a, b), c)

def heegner_reps(D, beta, N=32, Amax=200000):
    """One Heegner form [A,B,C] (N|A, B = beta mod 2N, primitive, disc D) per class of Cl(D).
    Returns dict reduced_form -> (A,B,C)."""
    reps = {}
    h = int(pari.qfbclassno(D))
    A = N
    while len(reps) < h and A <= Amax:
        for B in range(beta % (2*N), 2*A + 2*N, 2*N):
            if (B*B - D) % (4*A) == 0:
                C = (B*B - D)//(4*A)
                if gcd3(A, B, C) == 1:
                    r = reduce_form(A, B, C)
                    if r not in reps:
                        reps[r] = (A, B, C)
        A += N
    return reps
