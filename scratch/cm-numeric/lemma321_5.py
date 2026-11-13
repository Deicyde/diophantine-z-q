"""TYZ Lemma 3.21(1) (L2496-2512) for class 5 with g(n) = 1 (h(-4n) = 2: n = 5, 13, 37), for the
pinned z_n = (1 - [i]) f0(P_n) (cm-points' tyzZn) and Z(n) = z_n^t, t in Phi_0 = {1} or {sigma}.
A lift beta' of beta_1 acts on the genus field Q(i, sqrt n) by i -> i, sqrt n -> -sqrt n,
sqrt(-n) -> -sqrt(-n) (cm-points' betaOneSign).  Write beta' = c o u, c = complex conjugation
(iota_C), u in Gal(H'_n/K_n); then u(i) = -i, u acts non-trivially on H_n = K(i), and
z_n^{beta'} = (1 - [i]) c(u(f0 P_n)).  By CM.ShimuraReciprocity u(f0 P_n) = P_{pbar Q} for a split
prime p in a class of Pic(O_{n,4}) mapping to the non-trivial class of Cl(K_n) (all four such
classes are restrictions of lifts), and c(P) = conj(P) (CM.cmComplexConj).
Check: Z^{beta'} + Z - tau((1-i)/2) in {O, tau(1) = (0,0)}, tau((1-i)/2) = T - [i]T,
T = (2,-4), [i]T = (-2,-4i).  Also run with the opposite sign (1 + [i]) for comparison."""
from fractions import Fraction as Fr
from heeg import *
from shimura import pair_image
from class7 import add
from sigma5 import iP, sub

def conjP(P): return (pari.conj(P[0]), pari.conj(P[1]))
def classify(P):
    if P is None: return 'O'
    if abs(P[0]) + abs(P[1]) < pari('1e-300'): return '(0,0)'
    return f'other x={pari.precision(P[0], 8)}'.replace('\n', '')

T = (pari(2), pari(-4)); iT = (pari(-2), pari('-4*I'))
tau1mi = sub(T, iT)            # tau((1-i)/2) = T - [i]T
out = []
def say(*a):
    s = ' '.join(str(t) for t in a); print(s, flush=True); out.append(s)
say(f'tau((1-i)/2) = ({pari.precision(tau1mi[0],10)}, {pari.precision(tau1mi[1],10)})'.replace('\n',''))
for n in [5, 13, 37]:
    D = -64*n
    Q = (16*(n+1), -8, 1)
    f = xy(tau_of(*Q[:2], D))
    cnt = 0
    for p in range(3, 400):
        if cnt >= 4 or not pari.isprime(p) or pari.kronecker(-4*n, p) != 1: continue
        # p non-principal in O_K (Cl = Z/2): p is not a^2 + n b^2
        if any(((p - n*b*b) >= 0 and pari.issquare(p - n*b*b)) for b in range(0, 50)): continue
        bp = next(t for t in range(0, 2*p, 2) if (t*t - D) % (4*p) == 0)
        for sgnname, sgn in (('pbar', -1), ('p', 1)):
            Ilat = [(Fr(p), Fr(0)), (Fr(-bp, 2), Fr(sgn, 2))]
            Qp = pair_image(Q, Ilat, D)
            uf = xy(tau_of(*Qp[:2], D))
            res = []
            for nm, s in (('1-[i]', -1), ('1+[i]', 1)):
                def onepm(P): return add(P, iP(P)) if s == 1 else sub(P, iP(P))
                def onemp(P): return sub(P, iP(P)) if s == 1 else add(P, iP(P))
                # z = (1 + s[i]) f ; u(z) = (1 - s[i]) u(f) ; c(u z) = (1 + s[i]) c(u f)
                z = onepm(f)
                zb = onepm(conjP(uf))
                S = add(zb, z)
                res.append(f'{nm}: Z^b+Z-tau((1-i)/2) = {classify(sub(S, tau1mi) if S is not None else None)}')
            say(f'n={n} p={p} ({sgnname}): ' + ' ; '.join(res))
        cnt += 1
open('lemma321_5.out', 'w').write('\n'.join(out) + '\n')

# Second choice Phi_0 = {sigma}, sigma = sigma_varpi^2 generating Gal(H'_n/H_n): realized by a prime
# q = a^2 + n b^2 with a even, b odd ((a + b sqrt -n) mod 4 in the class of sqrt(-n): principal in
# O_K, not in <sigmaClass>).  Z = sigma(z_n) = (1 - [i]) P_{qbar Q}.
say('--- Phi_0 = {sigma} ---')
for n in [5, 13, 37]:
    D = -64*n
    Q = (16*(n+1), -8, 1)
    q = next(a*a + n*b*b for b in range(1, 99, 2) for a in range(2, 99, 2) if pari.isprime(a*a + n*b*b))
    a_, b_ = next((a, b) for b in range(1, 99, 2) for a in range(2, 99, 2) if a*a + n*b*b == q)
    bq = next(t for t in range(0, 2*q, 2) if (t - (-8*a_*pow(b_, -1, q))) % q == 0)
    Qs = pair_image(Q, [(Fr(q), Fr(0)), (Fr(-bq, 2), Fr(-1, 2))], D)
    fs = xy(tau_of(*Qs[:2], D))
    f = xy(tau_of(*Q[:2], D))
    z, zs = sub(f, iP(f)), sub(fs, iP(fs))
    say(f'n={n} q={q}=({a_})^2+{n}({b_})^2: sigma(z_n) - z_n = {classify(sub(zs, z))}')
    cnt = 0
    for p in range(3, 400):
        if cnt >= 2 or not pari.isprime(p) or pari.kronecker(-4*n, p) != 1: continue
        if any(((p - n*b*b) >= 0 and pari.issquare(p - n*b*b)) for b in range(0, 50)): continue
        bp = next(t for t in range(0, 2*p, 2) if (t*t - D) % (4*p) == 0)
        Qp = pair_image(Qs, [(Fr(p), Fr(0)), (Fr(-bp, 2), Fr(-1, 2))], D)
        uf = xy(tau_of(*Qp[:2], D))
        zb = sub(conjP(uf), iP(conjP(uf)))
        S = add(zb, zs)
        say(f'n={n} Phi0={{sigma}} p={p}: Z^b+Z-tau((1-i)/2) = {classify(sub(S, tau1mi) if S is not None else None)}')
        cnt += 1
open('lemma321_5.out', 'w').write('\n'.join(out) + '\n')
