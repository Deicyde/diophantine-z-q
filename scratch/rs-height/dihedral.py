"""J(u) = -57600 F^2/G^6 is the quotient map of P^1_u by the dihedral group D6 of Moebius maps
permuting the contacts; identify the CM factors of the genus-two quotient y^2 = F(u)."""
import sympy as sp
u = sp.symbols('u')
C = [0, -15, -20, -24, -30, -60]
F = sp.prod([u - c for c in C]); G = 7*u**2 + 300*u + 3600
J = -57600*F**2/G**6
maps = [u, -12*u/(u+12), -240*(u+15)/(13*u+240), -60*(u+60)/(7*u+240), -45*(u+20)/(2*u+45),
        -120*(u+30)/(7*u+180), -300*(u+24)/(11*u+300), -150*(u+24)/(7*u+150), -40*(u+30)/(u+40),
        -180*(u+20)/(7*u+120), -240*(u+15)/(7*u+60), 30*(u+60)/(u-30)]
print("J o g = J for all 12 maps:", all(sp.simplify(J.subs(u, g) - J) == 0 for g in maps))
rot = -60*(u+60)/(7*u+240)
print("fixed points of the order-6 rotation:", sp.factor(sp.numer(sp.together(rot - u))))
r = u
orders = []
for g in maps:
    h, k = g, 1
    while sp.simplify(h - u) != 0:
        h = sp.simplify(g.subs(u, h)); k += 1
    orders.append(k)
print("element orders:", sorted(orders))
# match Frobenius traces of the genus-two factors with Mordell curves y^2 = x^3 + k
def leg(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)
def ap(k, p):
    return -sum(leg(x**3 + k, p) for x in range(p))
target = {7: {4, -4}, 13: {-2}, 19: {8, -8}, 31: {4, -4}, 37: {-10}, 43: {8, -8}}
for k in [1, -1, 2, -2, 3, -3, 4, -4, 6, -6, 9, -9, 12, -12, 16, -16, 27, -27, 36, -36, 48, -48,
          108, -108, 432, -432]:
    tr = {p: ap(k, p) for p in target}
    if all(tr[p] in target[p] for p in target):
        print("y^2 = x^3 + %d has a_p" % k, tr)
