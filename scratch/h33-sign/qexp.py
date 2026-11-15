"""h33-sign: exact q-expansion checks (PARI via cypari2, exact integer series).

x = eta(2t)^2 eta(16t)/(eta(4t) eta(32t)^2) + 2,  y = -eta(8t)^4 eta(16t)^2/(eta(4t)^2 eta(32t)^4)
(the kernel's X0.xC, X0.yC).  Checks, exactly to O(q^N):
 (E) y^2 = x^3 + 4x                                            (leaf X0-EQ, sanity)
 (a) x(t+1/4) = -x(t), y(t+1/4) = I y(t)  [q -> I q]           (kernel: T321.xC_add_quarter, yC_add_quarter)
 (b) phi(-1/(32t)) = (2,-4) - phi(t): with X = x(W t) = 2 + 8 eta(2t)eta(16t)^2/(eta(t)^2 eta(8t)),
     Y = y(W t) = -4 eta(2t)^2 eta(4t)^4/(eta(t)^4 eta(8t)^2) (kernel X0.xC_fricke, yC_fricke, proved),
     the chord sum (2,-4) + (x,-y) equals (X(t'), Y(t')) as functions of t -- but X, Y are series in
     q = e^{2 pi i t} while (x, y) are evaluated at t too: the identity is phi(W t) + phi(t) = T, i.e.
     (X(t), Y(t)) = T - (x(t), y(t)).                           (kernel Shimura.etaModelFricke, proved)
"""
import cypari2, sys
pari = cypari2.Pari()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
q = pari('q')
def E(d):  # prod (1 - q^{dn}) to O(q^N)
    return pari(f'subst(eta(q + O(q^{N//d + 2})), q, q^{d})') + pari(f'O(q^{N})')
E1, E2, E4, E8, E16, E32 = (E(d) for d in (1, 2, 4, 8, 16, 32))
x = q**-2 * E2**2*E16/(E4*E32**2) + 2
y = -q**-3 * E8**4*E16**2/(E4**2*E32**4)
out = []
def rep(name, ser):
    v = pari.valuation(ser, q) if ser != 0 else None
    s = f'{name}: ' + ('exact zero to the series precision' if pari(f'truncate({ser})') == 0 else f'NONZERO, valuation {v}')
    s += f'  (precision O(q^{pari.serprec(ser, q)}))'
    print(s); out.append(s)
rep('(E) y^2 - x^3 - 4x', y**2 - x**3 - 4*x)
I = pari('I')
xs = pari.substpol(x, q, I*q) if False else pari(f'subst({x}, q, I*q)')
ys = pari(f'subst({y}, q, I*q)')
rep('(a) x(t+1/4) + x(t)', xs + x)
rep('(a) y(t+1/4) - I*y(t)', ys - I*y)
X = 2 + 8*q*E2*E16**2/(E1**2*E8)
Y = -4*E2**2*E4**4/(E1**4*E8**2)
lam = (-y + 4)/(x - 2)
x3 = lam**2 - 2 - x
y3 = -lam*(x3 - 2) + 4
rep('(b) X - x(T - P)', X - x3)
rep('(b) Y - y(T - P)', Y - y3)
# The other sign of the quarter shift would be x(t+1/4) = -x, y(t+1/4) = -I y: test it
rep('(a-) y(t+1/4) + I*y(t)   [expected NONZERO]', ys + I*y)
print('first coefficients: x =', pari(f'truncate({x} + O(q^6))'), '; y =', pari(f'truncate({y} + O(q^6))'))
open('qexp.out', 'w').write('\n'.join(out) + '\n')
