"""Check that TSHecke.lean contains the verbatim copies it claims (run from the repo root)."""
T = open('scratch/ts-hecke/TSHecke.lean').read()
def seg(path, a=None, b=None):
    L = open(path).read().split('\n')
    if a is None:
        return '\n'.join(L)
    return '\n'.join(L[a-1:b])
checks = [
    ('PropTSGlue.lean 3-3553 (prop-ts prefix, purity copy, Parts A-D incl. the five Hecke Props)',
     seg('scratch/prop-ts-glue/PropTSGlue.lean', 3, 3553)),
    ('AutOFinite.lean 3-1037', seg('scratch/aut-o-finite/AutOFinite.lean', 3, 1037)),
    ('SmoothStalk.lean 3-388', seg('scratch/infra-smooth-dim/SmoothStalk.lean', 3, 388)),
    ('CurveGlueAll.lean 1251-1253 (ComponentIrreducible)', seg('scratch/curve-glue/CurveGlueAll.lean', 1251, 1253)),
    ('CIproof.lean.part (all)', seg('scratch/curve-glue/CIproof.lean.part')),
]
ok = True
for name, s in checks:
    found = s in T
    ok &= found
    print(('CONTAINED   ' if found else 'MISSING     ') + name)
# the PropTS prefix of prop-ts-glue is itself scratch/prop-ts/PropTS.lean (prop-ts-glue's check)
pt = open('scratch/prop-ts/PropTS.lean').read().split('\n')
g = open('scratch/prop-ts-glue/PropTSGlue.lean').read().split('\n')
same = pt[:906] == g[:906]
print(('IDENTICAL   ' if same else 'DIFFERENT   ') + 'PropTSGlue.lean 1-906 vs scratch/prop-ts/PropTS.lean 1-906')
print('ALL OK' if ok and same else 'CHECK FAILED')
