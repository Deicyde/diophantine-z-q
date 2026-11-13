"""TYZ Theorem 3.6(1) (Period7.tex L1411-1413, 'CM point2'), third identity: for n = 5 (mod 8),
bar z_n = -z_n + tau(1), tau(1) = (0,0), bar = complex conjugation.  Tested for both candidate
translations z_n = (1 - [i]) f0(P_n) (cm-points' tyzZn) and (1 + [i]) f0(P_n), f0(P_n) = Heegner point
of [16(n+1), -8, 1] under iota_C (iota_C(i) = I)."""
from heeg import *
from class7 import add
from sigma5 import iP, sub
out = []
for n in [5, 13, 21, 29, 37, 53, 61]:
    D = -64*n
    f = xy(tau_of(16*(n+1), -8, D))
    r = []
    for nm, z in (('1-[i]', sub(f, iP(f))), ('1+[i]', add(f, iP(f)))):
        S = add((pari.conj(z[0]), pari.conj(z[1])), z)     # bar z + z, should be (0,0)
        if S is None: k = 'O'
        elif abs(S[0]) + abs(S[1]) < pari('1e-300'): k = '(0,0)'
        else: k = f'other x={pari.precision(S[0], 8)}'.replace('\n', '')
        r.append(f'{nm}: bar z + z = {k}')
    s = f'n={n}: ' + ' ; '.join(r); print(s); out.append(s)
open('conj5.out', 'w').write('\n'.join(out) + '\n')
