"""rv-blueprints: independent check of the Faltings normalization (bp-faltings AT3).
(1) pkg-I5's closed formula faltingsHeightEC for y^2 = x^3 + 1 (j = 0), computed by direct
    numerical integration: h = -log|Delta|/12 - (1/2) log(2 * int_C dlambda / |4x^3 + 4|).
(2) the eta-product form -(1/12) log(|eta(rho)|^24 (Im rho)^6) - log(2 pi) (an independent
    evaluation of the same archimedean quantity, by the Chowla-Selberg-type q-product).
(3) Deligne's recalled minimum -0.74875248 (j = 0, Deligne normalization; STANDARD, locator
    UNVERIFIED) minus (1/2) log pi should equal (1)."""
import mpmath as mp
mp.mp.dps = 20
# (1): integrate 1/|4x^3+4| over C in polar coordinates; use symmetry theta -> theta + 2pi/3.
f = lambda r, t: r / abs(4 * (r * mp.e**(1j * t))**3 + 4)
I = 3 * mp.quad(lambda r: mp.quad(lambda t: f(r, t), [0, mp.pi/3, 2*mp.pi/3]), [0, 0.5, 1, 2, mp.inf])
hypVol = 2 * I
hF = -mp.log(432) / 12 - mp.log(hypVol) / 2
# (2)
rho = mp.e**(2j * mp.pi / 3)
q = mp.e**(2j * mp.pi * rho)
eta = q**(mp.mpf(1)/24) * mp.qp(q)
hD = -(mp.log(abs(eta)**24 * mp.im(rho)**6)) / 12 - mp.log(2 * mp.pi)
print("hypVol =", hypVol)
print("faltingsHeightEC(y^2=x^3+1) =", hF)
print("eta-product form =", hD)
print("-0.74875248 - (1/2) log pi =", mp.mpf("-0.74875248") - mp.log(mp.pi) / 2)
