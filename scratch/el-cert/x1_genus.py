# X1: valuation check of M1 soundness; X2: genus of the theta=1 curve, original vs M1.
# Toy data: random small C_j in Q(sqrt2) (tests), R0 > 0 rational. Pure PARI via cypari2.
import random, cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
random.seed(1)
# X1: for k odd, all v(Theta0), v(q): Phi(B) (=> v(B) > 0 since v(B) odd) implies 2v(Theta0) < k
bad = 0
for k in range(1, 12, 2):
    for vT in range(-6, 12):
        for vq in range(-12, 12):
            va = min(0, k + 2*vq)          # v(1 - R0 q^2), no cancellation
            vB = k + 2*va - 2*vT
            assert vB % 2 == 1
            if vB > 0 and not (2*vT < k): bad += 1
print("X1 counterexamples:", bad)

def rnd(): return pari(random.randint(-9, 9)) / random.randint(1, 5)
def Wpair(Rq, Cs):
    # W = prod (1 + R C^2), C = c + d s, s^2 = 2; return (Wa, Wb) with W = Wa + Wb s (polys in q)
    Wa, Wb = pari(1), pari(0)
    for (c, d) in Cs:
        sa, sb = c*c + 2*d*d, 2*c*d                # C^2
        fa, fb = 1 + Rq*sa, Rq*sb
        Wa, Wb = Wa*fa + 2*Wb*fb, Wa*fb + Wb*fa
    return Wa, Wb
def genus_of(P):
    # genus of y^2 = P(q): from degree of squarefree part
    # squarefree test via gcd(P, P'); if squarefree the genus is (deg-1)//2
    g = pari.gcd(P, pari.deriv(P, 'q')); dg = int(pari.poldegree(g)); deg = int(pari.poldegree(P))
    # odd-multiplicity part has degree >= deg P - 2 deg gcd(P,P') (exact if squarefree)
    lb = deg - 2*dg
    return ("genus >=" if dg else "genus =", (lb - 1)//2, "deg", deg, "gcd deg", dg)
q = pari('q')
m = pari(3)
R0 = pari(7)/3
a = 1 - R0*q**2
def theta_num_den(Rq, groups):
    # Theta = Tr sum_g W_g^-1 = N/D with N, D in Q[q]
    N, D = pari(0), pari(1)
    for Cs in groups:
        Wa, Wb = Wpair(Rq, Cs)
        nrm = Wa*Wa - 2*Wb*Wb                      # W W^sigma
        tr = 2*Wa                                  # W + W^sigma
        N, D = N*nrm + tr*D, D*nrm                 # sum tr/nrm
    return N, D
for site, ngroups, ntests in [("test", 1, 6), ("slope", 6, 12)]:
    groups = [[(rnd(), rnd()) for _ in range(ntests)] for _ in range(ngroups)]
    for name, Rin in [("original", R0*a**2), ("M1", R0)]:
        N, D = theta_num_den(Rin, groups)
        gg = pari.gcd(N, D); N, D = N/gg, D/gg
        # B = R0 a^2 D^2 / N^2 ; theta = 1  <=>  m (m N^2 - R0 a^2 D^2) is a square
        P = m*(m*N**2 - R0*a**2*D**2)
        if name == "M1":
            g = pari.content(N); N, D = N/g, D/g   # constants in q
        print(site, name, "deg_q s =", int(pari.poldegree(a*D)) if name=="original" else 2,
              "genus, sqfree deg =", genus_of(P))
