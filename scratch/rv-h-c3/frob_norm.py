# Normalization check for C8's use of the lemma's weights {0,-1} (Tate convention, Q_l(1) weight -1).
# The Frobenius endomorphism pi_p of E mod p acts on T_l E as ARITHMETIC Frobenius; its trace is
# p+1-#E(F_p) (brute-force count here) and its det is p (=> det V_l E = cyclotomic, weights {0,-1}).
# Check: that trace equals the weight-2 newform coefficient a_p (Deligne/Tate normalization), p<200.
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**9)
curves = {"11a1": [0,-1,1,-10,-20], "37a1": [0,0,1,-1,0], "43a1": [0,1,1,0,0],
          "389a1": [0,1,1,-2,0], "5077a1": [0,0,1,-7,6]}
def count(a, p):
    a1,a2,a3,a4,a6 = a
    n = 1
    for x in range(p):
        for y in range(p):
            if (y*y + a1*x*y + a3*y - x**3 - a2*x*x - a4*x - a6) % p == 0:
                n += 1
    return n
for lab, a in curves.items():
    E = pari.ellinit(a)
    N = int(pari.ellglobalred(E)[0])
    ps = [p for p in range(2, 200) if pari.isprime(p) and N % p]
    tr = [p + 1 - count(a, p) for p in ps]
    mf = pari.mfinit([N, 2], 0)
    ok = False
    for f in pari.mfeigenbasis(mf):
        c = pari.mfcoefs(f, 200)
        if all(c[p] == t for p, t in zip(ps, tr)):
            ok = True
    print(lab, "N =", N, "#primes =", len(ps), "rational newform with a_p = p+1-#E(F_p):", ok)
