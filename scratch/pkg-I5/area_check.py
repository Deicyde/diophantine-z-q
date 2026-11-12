# Check: for y^2 = f(x), f cubic, omega = dx/y:
#   (i/2) * integral over E(C) of omega ^ conj(omega)  =  2 * integral_C dlambda(x) / |f(x)|
# The left side is the covolume of the period lattice of omega (PARI: E.omega).
# Partition of unity centred at the roots removes the 1/|x-a| singularities.
import mpmath as mp, cypari2
pari = cypari2.Pari()
mp.mp.dps = 20

def rhs(coeffs):  # coeffs of f, highest first, degree 3
    roots = mp.polyroots(coeffs)
    f = lambda x: mp.polyval(coeffs, x)
    total = 0
    for k, a in enumerate(roots):
        def g(r, t):
            x = a + r*mp.expj(t)
            w = [1/abs(x-b)**2 for b in roots]
            return r * (w[k]/sum(w)) / abs(f(x))
        total += mp.quad(g, [0, 0.5, 2, 10, mp.inf], [0, mp.pi, 2*mp.pi])
    return 2*total

def lhs(a1,a2,a3,a4,a6, scale):
    E = pari.ellinit([a1,a2,a3,a4,a6])
    w1, w2 = [complex(z) for z in E.omega()]
    area = abs((w1.conjugate()*w2).imag)
    return area*scale

# PARI's E.omega are the periods of dx/(2y+a1x+a3).
# y^2 = 4x^3 - 4x  <->  y'^2 = x^3 - x with y = 2y': omega = dx/y = dx/(2y') = PARI's differential
print("4x^3-4x   :", rhs([4,0,-4,0]), lhs(0,0,0,-1,0, 1.0))
# y^2 = 4x^3 + 4x + 4 <-> y'^2 = x^3+x+1
print("4x^3+4x+4 :", rhs([4,0,4,4]), lhs(0,0,0,1,1, 1.0))
# y^2 = x^3 - 2: omega = dx/y = 2 * dx/(2y): periods double, area * 4
print("x^3-2     :", rhs([1,0,0,-2]), lhs(0,0,0,0,-2, 4.0))
