"""theta-direct: generate the Lean lemmas `σ4/σ6` and `e²` values on the ten even characteristics (for
ThetaDirect/Modular.lean). Values from gt-theta's definitions (σ4, N4, σ6, N6 in ThetaModularityM46.lean)."""
import itertools
f2 = lambda x: x % 2
def sigma6(m):
    (a0, a1), (b0, b1) = m
    return ((f2(-b1), f2(b0)), (f2(a1 - b1 + 1 - b0), f2(-a0 + 2 * b0 + 2 + b1)))
def N6(m):
    (a0, a1), (b0, b1) = m
    return 4*a0*b0 + 4*a1*b1 - 2*b1**2 + 4*b1 - 4*b0**2 - 8*b0 - 4*b0*b1
def sigma4(m):
    (a0, a1), (b0, b1) = m
    return ((f2(a0 + b1), f2(a1 + b0)), (f2(a0 - 2*a1 + b1 - b0 + 1), f2(-2*a0 + 2*a1 + 2*b0 - b1 + 2)))
def N4(m):
    (a0, a1), (b0, b1) = m
    return (4*a0*a1 + 4*a1*b1 + 4*a0*b0 - 2*(a0 + b1)**2 - 4*(a0 + b1) - 4*(a1 + b0)**2 - 8*(a1 + b0)
            + 4*(a0 + b1)*(a1 + b0))
even = [m for m in itertools.product(itertools.product((0, 1), repeat=2), repeat=2)
        if (m[0][0]*m[1][0] + m[0][1]*m[1][1]) % 2 == 0]
L = lambda m: f'(![{m[0][0]}, {m[0][1]}], ![{m[1][0]}, {m[1][1]}])'
nm = lambda m: f'{m[0][0]}{m[0][1]}{m[1][0]}{m[1][1]}'
out = []
for M, sig, N in [('6', sigma6, N6), ('4', sigma4, N4)]:
    for m in even:
        out.append(f'theorem σ{M}_{nm(m)} : GapTheta.σ{M} {L(m)} = {L(sig(m))} := by decide')
    for m in even:
        k = N(m); assert k % 2 == 0; j = k // 2
        val = '1' if j % 2 == 0 else '-1'
        out.append(f'theorem e{M}_{nm(m)} : cexp (π * I * (GapTheta.N{M} {L(m)} : ℂ) / 4) ^ 2 = {val} := by\n'
                   f'  rw [e_sq_val _ ({j}) (by decide)]; norm_num')
    out.append('')
open('scratch/theta-direct/py/gen_modular.out', 'w').write('\n'.join(out))
print('\n'.join(out[:3]))
print(len(out))
