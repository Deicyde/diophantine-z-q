# Numerically compute periods of Phi_d = sum a_n/n q^n over Gamma0(32 d^2) in the basis of the
# period lattice L of C_d : y^2 = x^3 - d^2 x (g2 = 4 d^2, g3 = 0), to find C = {c : c Lambda_f in L}.
import sys, cypari2, random
pari = cypari2.Pari(); pari.set_real_precision(40); pari.allocatemem(2*10**9)
d = int(sys.argv[1]); N = 32*d*d
E = pari.ellinit([-d*d, 0]); 
w1, w2 = E.omega()  # PARI periods, for dx/(2y) ? PARI uses dx/(2y+a1x+a3)
an = pari.ellan(E, 40000)
import cmath, math
def Phi(tau, M):
    q = cmath.exp(2j*math.pi*tau); s = 0; qn = 1
    for n in range(1, M+1):
        qn *= q; s += complex(an[n-1])/n*qn
    return s
w1 = complex(w1); w2 = complex(w2)
random.seed(1)
res = []
for k in range(1, 4):
  for dd in range(1, 30):
    c = N*k
    if math.gcd(c, dd) != 1: continue
    # a*dd - b*c = 1
    a = pow(dd, -1, c); b = (a*dd - 1)//c
    tau = complex(-dd/c, 1.0/c)
    gt = (a*tau + b)/(c*tau + dd)
    M = int(40*c/(2*math.pi))+10
    if M > 39000: continue
    p = Phi(gt, M) - Phi(tau, M)
    # solve p = x w1 + y w2
    det = (w1.conjugate()*w2).imag
    x = (p.conjugate()*w2).imag/det; y = (w1.conjugate()*p).imag/det
    res.append((k, dd, round(x, 6), round(y, 6)))
    if len(res) >= 12: break
  if len(res) >= 12: break
print("d", d, "omega", w1, w2)
for r in res: print(r)
