"""Check that declarations copied from other tasks are textually identical to their sources."""
import re, sys, os
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.normpath(os.path.join(here, '..', '..'))
def decl(text, name):
    # the declaration block starting at 'theorem name' up to the next blank line
    i = text.index('theorem ' + name)
    j = text.find('\n\n', i)
    return text[i:j if j >= 0 else len(text)]
src = open(os.path.join(root, 'g0-dim/part_dim.lean')).read()
ok = True
for f in ['Alg.lean', 'Dim.lean']:
    mine = open(os.path.join(root, 'curve-infra', f)).read()
    names = ['ringKrullDim_eq_of_isIntegral_of_injective', 'ringKrullDim_mvPolynomial_field']
    if f == 'Dim.lean':
        names += ['topologicalKrullDim_eq_iSup_of_openEmbedding', 'scheme_dim_eq_of_iso', 'spec_dim']
    for n in names:
        r = decl(src, n) == decl(mine, n)
        ok &= r
        print(f, n, 'IDENTICAL' if r else 'DIFFERENT')
ss = open(os.path.join(root, 'infra-smooth-dim/SmoothStalk.lean')).read().split('\n')[1:526]
allf = open(os.path.join(root, 'curve-infra/CurveInfraAll.lean')).read().split('\n')[2:527]
r = ss == allf
ok &= r
print('CurveInfraAll.lean lines 3-527 vs SmoothStalk.lean lines 2-526', 'IDENTICAL' if r else 'DIFFERENT')
print('ALL OK' if ok else 'MISMATCH')
