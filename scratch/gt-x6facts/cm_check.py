# gt-x6facts: arithmetic sanity checks of the CM data on X6 (PARI via cypari2).
# (1) class numbers and splitting of 2, 3 in Q(i), Q(sqrt-3), Q(sqrt-6): GR Thm 5.12 prediction of [Q(x):Q].
# (2) Elkies' conic Y^2 + 3X^2 + 3Z^2 = 0, t = -X^2/Z^2: residue fields of the points over t = 1, infinity, 0.
# (3) the Mobius map j = 16(t - 1)/27 sends (t=1, inf, 0) to the chain's values (0, inf, -16/27).
import cypari2
pari = cypari2.Pari()
for D, name in [(-4, 'Z[i]'), (-3, 'Z[zeta3]'), (-24, 'Z[sqrt-6]')]:
    h = pari.qfbclassno(D)
    inert = [p for p in (2, 3) if pari.kronecker(D, p) == -1]
    split = [p for p in (2, 3) if pari.kronecker(D, p) == 1]
    b = len(inert)
    deg = (1 if b == 0 else 2) * h
    print(f"D={D} {name}: h={h} inert={inert} split={split} b={b} predicted [Q(x):Q]={deg} (k in Q(x): {b != 0}); count 2^b h = {2**b*h}")
# conic points
x = pari('x')
print("t=1: X^2=-Z^2, Y^2=-3X^2-3Z^2=0 -> X/Z root of", pari('x^2+1'), "-> Q(i)")
print("t=inf: Z=0, Y^2=-3X^2 -> Y/X root of", pari('x^2+3'), "-> Q(sqrt-3)")
print("t=0: X=0, Y^2=-3Z^2 -> Y/Z root of", pari('x^2+3'), "-> Q(sqrt-3)")
print("Q(sqrt-3) contains Q(sqrt-6)?", pari.nfisincl(pari('x^2+6'), pari('x^2+3')) != 0)
from fractions import Fraction as F
j = lambda t: F(16) * (t - 1) / 27
print("j(1) =", j(F(1)), " j(0) =", j(F(0)), " j(inf) = inf")
