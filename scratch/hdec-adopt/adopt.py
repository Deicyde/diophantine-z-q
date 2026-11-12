# Generate ZInQKernel/HDecomp/ modules from the scratch drafts (run from the worktree root).
import re, os
S = 'scratch/'; D = 'ZInQKernel/HDecomp/'
DOC = ('/-! Glue of `docs/research/h-decomposition.md` (from `scratch/{src}`, task hdec-adopt).\n'
       'The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/\n')
def emit(dst, src, lines, imports):
    out = []
    body = [l for l in lines if not l.startswith('import ')]
    body = [l for l in body if not re.match(r'#(print|check|eval|exit)', l)]
    out += ['import ' + i + '\n' for i in imports]
    out.append('\n'); out.append(DOC.format(src=src)); out.append('\n')
    out += body
    os.makedirs(os.path.dirname(D + dst), exist_ok=True)
    open(D + dst, 'w').write(''.join(out))
def rd(p): return open(S + p).read().splitlines(keepends=True)
def imps(lines, m={}):
    r = []
    for l in lines:
        if l.startswith('import '):
            x = l.split()[1]; r.append(m.get(x, x))
    return r
def plain(dst, src, m={}):
    L = rd(src); emit(dst, src, L, imps(L, m))
H = 'ZInQKernel.HDecomp.'
plain('Objects.lean', 'obj-bridge/Objects.lean')
# Descent
dm = {f'GlueDescent.{f}': H + 'Descent.' + f for f in
      'ProjRep B1Quat Cochain Constants Chi B2Glue B2Assembly B3Assembly'.split()}
for f in 'ProjRep B1Quat Cochain Constants Chi B2Glue B2Assembly B3Assembly'.split():
    plain(f'Descent/{f}.lean', f'glue-descent/{f}.lean', dm)
# Conductor
for f in 'Breaks Dyadic Level'.split():
    plain(f'Conductor/{f}.lean', f'glue-conductor/{f}.lean')
for f in 'I6Base Inflation SqrtChar'.split():
    plain(f'Conductor/{f}.lean', f'glue-I6-rest/{f}.lean')
L = rd('glue-I6-rest/Conductor.lean')
i0 = next(i for i, l in enumerate(L) if l.startswith('section Ramification'))
i1 = next(i for i, l in enumerate(L) if l.startswith('section Proof'))
j = next(i for i, l in enumerate(L) if l.startswith('section Conductor'))
k = next(i for i, l in enumerate(L) if l.startswith('noncomputable def codimInv'))
body = L[:i0] + L[j:k] + L[i1:]
body = [l.replace('are copied verbatim from `scratch/pkg-I6/I6.lean` (Part II).',
                  'are imported from `I6Base` (pkg-I6, Part II).') for l in body]
emit('Conductor/ArtinUpper.lean', 'glue-I6-rest/Conductor.lean', body, [H + 'Conductor.I6Base'])
L = rd('glue-d1-local/Local.lean')
emit('Conductor/D1Local.lean', 'glue-d1-local/Local.lean', L[402:], [H + 'Conductor.Breaks'])
# A6
plain('A6/A6.lean', 'glue-a6-alg/A6.lean'); plain('A6/Extend.lean', 'glue-a6-alg/Extend.lean')
# C10
plain('C10/C10.lean', 'glue-c10/C10.lean')
L = rd('glue-c10/Trace.lean')
a = next(i for i, l in enumerate(L) if l.startswith('def CharPolyIndepOfEll'))
b = next(i for i, l in enumerate(L) if i > a and l.startswith('/--'))
c = 336  # line 337 = `namespace PkgI3` of the C10 part
hdr = ['/-\nglue-c10: the ℓ-independence of traces (C10), over pkg-I3\'s definitions as imported\n'
       'from `ZInQKernel.HDecomp.Objects` (§A of obj-bridge, verbatim pkg-I3).\n-/\n',
       'noncomputable section\n\n']
emit('C10/Trace.lean', 'glue-c10/Trace.lean', hdr + L[c:a - 1] + L[b:], [H + 'Objects'])
# Repo
for f in 'A1Quaternion Numerics PRArith TorsionFree'.split():
    plain(f'Repo/{f}.lean', f'glue-repo/{f}.lean')
# Assembly: GlueAssembly.lean with F4Copy's verbatim JHeight part replaced by an import
L = rd('glue-assembly/GlueAssembly.lean')
emit('Assembly.lean', 'glue-assembly/GlueAssembly.lean', L, imps(L))
