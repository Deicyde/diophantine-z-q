import time, random
from fractions import Fraction as Fr
import slopelib as L
rng = random.Random(1)
H = [331, 337]
Sb = L.S_HT + H
t0=time.time(); e0 = L.ell0(H); print("ell0 digits", L.gmpy2.num_digits(e0,10), time.time()-t0)
v = 2**6 * 3**7; u = 1000003
t = Fr(u, v)
print("F>0", L.F(t) > 0)
Spole = [l for l in Sb if not L.field2_holds(t, l) and L.lemmaP_hyp(t, l)]
print("Spole", Spole)
Nl = {l: 23 * L.vp_int(v, l) + L.vp_int(12, l) + 2 for l in Spole}
t0=time.time()
q, info = L.choose_q(t, 1, Sb, Spole, Nl, [], [], e0)
print("q", info, "digits", L.gmpy2.num_digits(L.mpz(q.denominator),10), time.time()-t0)
D = L.model_tests([], rng)
P = L.PoleInput(t, 1, q, e0, D)
for l in L.S0 + [11]:
    t0=time.time(); r = P.local(l); print(l, "v(a)=", P.v_a(l), r, round(time.time()-t0,2))
print(P.real()['B'])
