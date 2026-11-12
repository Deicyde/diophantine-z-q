# Stable Faltings height of an elliptic curve E/Q, original Faltings normalization, two ways:
#  (I)  integral form used in I5.lean:  (1/12)(finpart(j) - log|Delta|) - (1/2) log Area,
#       Area = covolume of the period lattice of omega = dx/(2y+a1x+a3)  (PARI E.omega())
#  (II) Silverman 1986 Prop 1.1 / BCCGM (6.2):
#       (1/12)(finpart(j) - log((2pi)^12 |eta(tau)|^24 Im(tau)^6))
# finpart(j) = sum over finite v of log max(1,|j|_v) = log(denominator of j) for j in Q.
# Expected (j = 0): Deligne's minimum -0.74875... minus (1/2) log pi = -1.3211...
import cypari2, math
pari = cypari2.Pari()
def check(ainv):
    E = pari.ellinit(ainv)
    w1, w2 = [complex(z) for z in E.omega()]
    area = abs((w1.conjugate()*w2).imag)
    j = pari('ellinit(%s).j' % str(ainv))
    D = float(pari('ellinit(%s).disc' % str(ainv)))
    fin = math.log(float(pari.denominator(j)))
    I = (fin - math.log(abs(D)))/12 - 0.5*math.log(area)
    tau = pari('my(E=ellinit(%s),w=E.omega,t=w[2]/w[1]); if(imag(t)<0,t=-t); t' % str(ainv))
    tau = pari.redimag(tau) if hasattr(pari,'redimag') else tau
    eta = complex(pari.eta(tau, 1))
    t = complex(tau)
    II = (fin - math.log((2*math.pi)**12 * abs(eta)**24 * t.imag**6))/12
    print(ainv, "j =", j, " (I) %.6f  (II) %.6f" % (I, II))
for a in ([0,0,0,0,1], [0,0,1,0,0], [0,0,0,-1,0], [0,-1,1,-10,-20], [0,-1,1,0,0], [1,0,0,-1,0], [0,0,0,-2,1]):
    check(a)
print("Deligne min - (1/2)log pi =", -0.74875248 - 0.5*math.log(math.pi))
