# Ground-truth check (PARI via cypari2) of the statements behind Continuation.lean:
#  (1) a_n(C_d) = J(d'|n) * a_n(C_1) for n <= 300, d' the squarefree part of d (d = m^2 d'):
#      for squarefree d this is cdCoeff_twist + LSeries_cd_eq'; for non-squarefree d it also
#      checks LFunction_cd_sq_mul (C_{m^2 d'} ~ C_{d'}).
#  (2) for squarefree d, the model y^2 = x^3 - d^2 x is minimal at every p (PARI ellglobalred
#      gives the change of variables to the global minimal model; u = 1) and the reduction at
#      every p | 2d is additive (no multiplicative reduction).
import cypari2
pari = cypari2.Pari()
N = 300
E1 = pari.ellinit([0, 0, 0, -1, 0])
a1 = pari.ellan(E1, N)
ds = [1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 21, 22, 30, 34, 4, 8, 9, 12, 18, 20, 25, 27, 45, 50, 72]
fails = 0
for d in ds:
    E = pari.ellinit([0, 0, 0, -d * d, 0])
    an = pari.ellan(E, N)
    dp = int(pari.core(d))
    bad = [n for n in range(1, N + 1)
           if int(an[n - 1]) != int(pari.kronecker(dp, n)) * int(a1[n - 1])
           and n % 2 == 1]
    # even n: a_n(C_1) = 0, check a_n(C_d) = 0
    bad += [n for n in range(2, N + 1, 2) if int(an[n - 1]) != 0]
    gr = pari.ellglobalred(E)
    cond = int(gr[0]); u = gr[1][0]
    sqf = bool(pari.issquarefree(d))
    kod = {}
    for p in pari.factor(2 * d)[0]:
        loc = pari.elllocalred(E, p)
        kod[int(p)] = (int(loc[0]), int(loc[1]))  # (conductor exponent f_p, Kodaira code)
    mult = [p for p, (f, k) in kod.items() if f == 1]
    line = f"d={d:3d} core={dp:3d} sqfree={sqf!s:5} cond={cond} = {pari.factor(cond)} u={u} (f_p,kod)={kod} " \
           f"twist_mismatch={len(bad)} mult_red={mult}"
    if bad or mult or (sqf and u != 1):
        fails += 1
        line += "  <-- FAIL"
    print(line)
print("failures:", fails)
