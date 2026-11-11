"""E4: minimal-genus redesign. If Θ did not depend on q (Θ0 constant on an honest line), the sound
double-cover gadget m(m - B) ∈ Q² with B = R0 a²/Θ0², a = 1 - R0 q², needs a rational point on
   C_m : h² = m(m Θ0² - R0 (1 - R0 q²)²)     (genus 1; Theorem G forbids genus 0).
30 toy samples: R0 = p·u (p prime > 324, v_p(R0) = 1), Θ0 = random rational; m over the 16 positive divisors
of 2730. Record: for how many samples some m gives a point of height <= 2000 (hyperellratpoints), and the
rank of Jac(C_m) (ellrank) for the first m with an everywhere-locally-soluble... (rank bounds only)."""
import random, cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
random.seed(3)
M = [d for d in range(1, 2731) if 2730 % d == 0][:16]
from sympy import prime
def jac(a, b, c, d, e):
    I = 12*a*e - 3*b*d + c*c; J = 72*a*c*e + 9*b*c*d - 27*a*d*d - 27*e*b*b - 2*c**3
    return pari.ellinit([0, 0, 0, -27*I, -27*J])
found = 0; rk_hist = {}
for s in range(30):
    p = prime(random.randint(70, 200)); u = random.choice([x for x in range(1, 40) if x % p])
    R0 = p*u; T0 = pari(f"{random.randint(1,60)}/{random.randint(1,60)}")
    got = None; ranks = []
    for m in M:
        # h² = m(mT0² - R0(1 - R0 q²)²) = -m R0³ q⁴ + 2 m R0² q² + m(m T0² - R0)
        a4 = -m*R0**3; a2 = 2*m*R0**2; a0 = m*(m*T0**2 - R0)
        den = int(pari.denominator(a0)); a4 *= den*den; a2 *= den*den; a0 = a0*den*den   # scale h by den
        P = pari(f"{a4}*x^4 + {a2}*x^2 + ({a0})")
        pts = pari.hyperellratpoints(P, 2000)
        E = jac(a4, 0, a2, 0, a0)
        r = pari.ellrank(E)
        ranks.append((int(r[0]), int(r[1])))
        if len(pts) > 0 and got is None: got = (m, str(pts[0]))
    if got: found += 1
    lo = max(r[0] for r in ranks); rk_hist[lo] = rk_hist.get(lo, 0) + 1
    print(s, "R0", R0, "Θ0", T0, "point:", got, "max rank lower bound over m:", lo)
print("samples with a point for some m:", found, "/ 30; histogram of max rank lower bound:", rk_hist)
