# Generate ZInQKernel/HDecomp/ modules from the scratch drafts (run from the worktree root).
import re, os
S = 'scratch/'; D = 'ZInQKernel/HDecomp/'
DOC = ('/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from\n'
       '`scratch/{src}`.\n'
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
q = D + 'Descent/B2Assembly.lean'; t = open(q).read()
i = t.index('Compile (out of tree'); j = t.index('-/', i)
open(q, 'w').write(t[:i] + 'Built in the project as `ZInQKernel.HDecomp.Descent.B2Assembly`.\n' + t[j:])
# Conductor
for f in 'Breaks Dyadic Level'.split():
    plain(f'Conductor/{f}.lean', f'glue-conductor/{f}.lean')
for f in 'Inflation SqrtChar'.split():
    plain(f'Conductor/{f}.lean', f'glue-I6-rest/{f}.lean')
# I6Base: the verbatim copy of `GlueConductor.exists_sq_eq_one_add` becomes a call to it
L = rd('glue-I6-rest/I6Base.lean')
a = next(i for i, l in enumerate(L) if l.startswith('theorem exists_sq_eq_one_add'))
b = next(i for i in range(a, len(L)) if L[i].rstrip().endswith(':= by'))
c = next(i for i in range(b + 1, len(L)) if L[i].strip() and not L[i].startswith(' '))
while not L[c - 1].strip(): c -= 1
L = L[:b] + [L[b].rstrip()[:-len(':= by')] + ':=\n',
             '  GlueConductor.exists_sq_eq_one_add e s hs h2 z hz\n'] + L[c:]
L = [l.replace('/-! Adopted verbatim from glue-conductor', '/-! Imported from glue-conductor') for l in L]
emit('Conductor/I6Base.lean', 'glue-I6-rest/I6Base.lean', L, imps(L) + [H + 'Conductor.Dyadic'])
L = rd('glue-I6-rest/Conductor.lean')
i0 = next(i for i, l in enumerate(L) if l.startswith('section Ramification'))
i1 = next(i for i, l in enumerate(L) if l.startswith('section Proof'))
j = next(i for i, l in enumerate(L) if l.startswith('section Conductor'))
k = next(i for i, l in enumerate(L) if l.startswith('noncomputable def codimInv'))
body = L[:i0] + L[j:k - 1] + ["open IsLocalRing\n\n"] + L[i1:]
body = [l.replace('are copied verbatim from `scratch/pkg-I6/I6.lean` (Part II).',
                  'are imported from `I6Base` (pkg-I6, Part II).') for l in body]
emit('Conductor/ArtinUpper.lean', 'glue-I6-rest/Conductor.lean', body, [H + 'Conductor.I6Base'])
L = rd('glue-d1-local/Local.lean')
emit('Conductor/D1Local.lean', 'glue-d1-local/Local.lean', L[402:], [H + 'Conductor.Breaks'])
# A6
L = rd('glue-a6-alg/A6.lean')
a = next(i for i, l in enumerate(L) if l.rstrip() == 'namespace GlueA6Alg')
b = next(i for i, l in enumerate(L) if l.startswith('/-! ## 10. rv-a6-route'))
mid = ['namespace GlueA6Alg\n\n',
       "/-! §1-§9 (pkg-I2's definitions, leaves and proved glue, copied verbatim in the scratch\n",
       'draft) are imported from `ZInQKernel.HDecomp.Objects` (§B, namespace `PkgI2`). -/\n\n',
       'open PkgI2\n\n', 'section Glue\n\n', 'variable {K : Type u} [Field K]\n\n']
emit('A6/A6.lean', 'glue-a6-alg/A6.lean', L[:a] + mid + L[b:], imps(L) + [H + 'Objects'])
plain('A6/Extend.lean', 'glue-a6-alg/Extend.lean')
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
# Assembly: GlueAssembly.lean (= F2, Ext, Transfer, F4Copy, Assembly) with F4Copy's verbatim copy
# of `ZInQKernel/Hypotheses/JHeight.lean` replaced by an import of that module.
parts = []
for f in 'F2 Ext Transfer'.split():
    parts += [l for l in rd(f'glue-assembly/{f}.lean') if not l.startswith('import ')] + ['\n']
F4 = rd('glue-assembly/F4Copy.lean')
a = next(i for i, l in enumerate(F4) if l.startswith('def SixContactMinAt')) - 2
f4 = ['/-! F4 (from `scratch/glue-assembly/F4Copy.lean`): the copy of `JHeight.lean` is replaced by\n',
      'an import of `ZInQKernel.Hypotheses.JHeight`; `SixContactMinAt S` is `SixContactMin` at\n',
      '`S = Mult.S_mul` by `rfl`. -/\n\n', 'namespace GlueAssembly\n\n', 'open ZInQ ZInQ.JHeight\n\n']
f4 += [l for l in F4[a:] if not l.startswith('theorem heightH6_eq')]
parts += f4 + ['\n'] + rd('glue-assembly/Assembly.lean')
parts = [l.replace('open Real ZInQ Height', 'open Real ZInQ ZInQ.JHeight Height') for l in parts]
emit('Assembly.lean', 'glue-assembly/GlueAssembly.lean', parts,
     ['Mathlib', 'ZInQKernel.Compiler.Precision.HeightConstant', 'ZInQKernel.Hypotheses.JHeight'])

import subprocess, glob
subprocess.run(['python3', '-I', 'scratch/hdec-adopt/wrap.py'] + sorted(glob.glob(D + '**/*.lean', recursive=True)))
