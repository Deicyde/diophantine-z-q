# C_m: h^2 = a q^4 + b q^2 + c, a=-m R0^3, b=2 m R0^2, c=m(m Th^2 - R0).
# Classical Jacobian y^2 = x^3 - 27 I x - 27 J (I = 12ac + b^2, J = 72abc - 2b^3).
# Claim: Jac(C_m) = E_J: y^2 = x(x^2 - 2b x + b^2 - 4ac) = x(x^2 - 4 m R0^2 x + 4 m^3 R0^3 Th^2),
# 2-isogenous to E: y^2 = x(x^2 + b x + a c); C_m is the covering of class d = a = -m R0 (mod squares)
# for the isogeny E -> E_J, i.e. C_m(Q) != empty iff -m R0 in x(E(Q)) mod Q*^2 (x(O)=1, x(0,0)=ac).
import random; from fractions import Fraction as Fr
import cypari2; pari = cypari2.Pari()
random.seed(5); good = 0
for trial in range(20):
    m = random.choice([1,-1,2,-2,3,-3,5,-5,6,7,-7,13]); R0 = random.randint(2, 999)
    Th = Fr(random.randint(1, 999), random.randint(1, 99))
    a, b, c = -m*R0**3, 2*m*R0**2, m*(m*Th*Th - R0)
    I = 12*a*c + b*b; J = 72*a*b*c - 2*b**3
    E1 = pari.ellinit([0, 0, 0, str(-27*I), str(-27*J)])
    EJ = pari.ellinit([0, -4*m*R0**2, 0, str(4*m**3*R0**3*Th*Th), 0])
    N = pari.numerator(E1[11]) * pari.denominator(E1[11]) * pari.numerator(EJ[11]) * pari.denominator(EJ[11])
    same = E1[12] == EJ[12] and all(pari.ellap(E1, p) == pari.ellap(EJ, p) for p in pari.primes(80)[3:] if N % p)
    good += bool(same)
print("Jac(C_m) = x(x^2 - 4mR0^2 x + 4m^3R0^3Th^2):", good, "/ 20")
