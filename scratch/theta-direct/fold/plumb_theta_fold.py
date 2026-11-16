"""theta-fold step 1 (plumbing): the consumer of `G0Split.ThetaPt.ThetaRatiosAlgebraic` (TailK's
`gluePieces_of_open4`, through `thetaPointOfFibre_of_qm_ratios`) takes theta-split's use form instead.

* theta-split's `ThetaSplit.ThetaRatiosAtQM`, `Jmap_ne_zero`, `thetaPointOfFibre_of_qm_atQM` (scratch/linyang-printed/
  LinYangPrintedFull.lean l.660-712, igusa-alg's verbatim copy of scratch/theta-split/ThetaUse.lean §1) move into
  TailK, unchanged, in namespace `HDec.HSyn.G0Split.ThetaPt.ThetaSplit`, right before `gluePieces_of_open4`.
* `gluePieces_of_open4` gets the binder `hθ : PkgI1.QMHauptmodul → ThetaSplit.ThetaRatiosAtQM` and proves `thetaPoint`
  by `thetaPointOfFibre_of_qm_atQM (…) (hθ l.qmHauptmodul)`; `l.thetaRatiosAlgebraic` is no longer read.
* `sixContactMin_of_open4`, `_open6` … `_open28` take `hθ` and pass it on; the example after `_open6` gets the binder.
Run from the repository root."""
import re
H = 'ZInQKernel/OneProof/H/'
SRC = 'scratch/theta-fold/src/LinYangPrintedFull.lean'
files = {}
def get(f):
    if f not in files: files[f] = open(f).read()
    return files[f]
def put(f, s): files[f] = s
def sub1(f, old, new):
    s = get(f); n = s.count(old)
    assert n == 1, (f, old[:80], n)
    put(f, s.replace(old, new))
decl_start = re.compile(r'^(theorem|def|lemma|structure|example|/--|#print|end |namespace |open |section)')
def span(s, name):
    L = s.split('\n')
    hits = [i for i, l in enumerate(L) if re.match(r'^theorem ' + re.escape(name) + r'[\s(]', l)]
    assert len(hits) == 1, (name, hits)
    i = hits[0]; j = i + 1
    while j < len(L) and L[j].strip() != '' and not decl_start.match(L[j]): j += 1
    return L, i, j
def edit_decl(f, name, pairs):
    s = get(f); L, i, j = span(s, name)
    body = '\n'.join(L[i:j])
    for old, new in pairs:
        assert body.count(old) == 1, (name, old, body.count(old))
        body = body.replace(old, new)
    L[i:j] = body.split('\n'); put(f, '\n'.join(L))

BINDER = '(hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)'

# --- the moved block (theta-split §1 without the verbatim-copy check of §0)
src = open(SRC).read().split('\n')
a = next(i for i, l in enumerate(src) if l.startswith('/-- **GLUE (G19 / F1, the use of `ThetaRatiosAlgebraic`'))
b = next(i for i, l in enumerate(src) if l.startswith('/-! ## 2. Reduction to symmetric functions'))
moved = '\n'.join(src[a:b]).rstrip()
assert moved.count('def ThetaRatiosAtQM : Prop :=') == 1 and moved.count('theorem thetaPointOfFibre_of_qm_atQM') == 1
assert moved.count('theorem Jmap_ne_zero') == 1 and moved.count('\ntheorem ') + moved.count('\ndef ') == 3
block = ('/-! ### theta-fold: the use form of `ThetaRatiosAlgebraic` (theta-split, moved here unchanged)\n\n'
         'theta-split\'s `ThetaRatiosAtQM` (scratch/theta-split/ThetaUse.lean §1, via igusa-alg and linyang-printed) is how\n'
         '`gluePieces_of_open4` uses the theta algebraicity: only along pkg-I1\'s QM period matrices `Ω(τ)`. igusa-alg and\n'
         'linyang-printed prove it from the printed leaves `IgusaThetaExpressions` and `LinYangEx29All` (with `QMHauptmodul`;\n'
         '`ZInQKernel/Contrib/OneProof/LinYangPrinted.lean`), which replace the universal field `thetaRatiosAlgebraic`. -/\n\n'
         'namespace G0Split.ThetaPt.ThetaSplit\n\n'
         'open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings\n'
         'open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst\n'
         '  absLogHeight)\n'
         'open Complex Polynomial\n\n' + moved + '\n\nend G0Split.ThetaPt.ThetaSplit\n\n')
K = H + 'TailK.lean'
s = get(K)
anchor = '/-- **Leaves.lean\'s `GluePieces` from leaf-fold4\'s open statements**'
assert s.count(anchor) == 1
put(K, s.replace(anchor, block + anchor))
edit_decl(K, 'gluePieces_of_open4', [
    ('(l : OpenAddedLeaves4) (g : OpenGlue4) (hYu : QMLattice.YuB6Alg) : GluePieces :=',
     '(l : OpenAddedLeaves4) (g : OpenGlue4) (hYu : QMLattice.YuB6Alg)\n    ' + BINDER + ' : GluePieces :='),
    ('thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios', 'thetaPoint := G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_atQM'),
    ('      l.thetaRatiosAlgebraic\n', '      (hθ l.qmHauptmodul)\n')])
edit_decl(K, 'sixContactMin_of_open4', [
    ('(hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=', '(hYu : QMLattice.YuB6Alg)\n    ' + BINDER + ' : ZInQ.SixContactMin :='),
    ('(gluePieces_of_open4 r t l g hYu) h20', '(gluePieces_of_open4 r t l g hYu hθ) h20')])

chain = [('TailO', 6), ('TailX', 7), ('TailZ4', 8), ('TailZ9', 9), ('TailZ11', 10), ('TailZ13', 11), ('TailZ15', 12),
         ('TailZ17', 13), ('TailZ18', 14), ('TailZ19', 15), ('TailZ22', 16), ('TailZ23', 17), ('TailZ24', 18),
         ('TailZ25', 19), ('TailZ26', 20), ('TailZ27', 21), ('TailZ28', 22), ('TailZ29', 23), ('TailZ30', 24),
         ('TailZ31', 25), ('TailZ32', 26), ('TailZ33', 27), ('TailZ34', 28)]
for mod, n in chain:
    f = H + mod + '.lean'
    s = get(f); L, i, j = span(s, f'sixContactMin_of_open{n}')
    body = '\n'.join(L[i:j])
    assert body.count(') : ZInQ.SixContactMin :=') == 1, n
    body = body.replace(') : ZInQ.SixContactMin :=', ')\n    ' + BINDER + ' : ZInQ.SixContactMin :=')
    body = body.rstrip() + ' hθ'
    L[i:j] = body.split('\n'); put(f, '\n'.join(L))
sub1(H + 'TailO.lean', '''    (_ : HDec.QMLattice.YuB6Alg), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open6''', '''    (_ : HDec.QMLattice.YuB6Alg)
    (_ : HDec.PkgI1.QMHauptmodul → HDec.HSyn.G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open6''')
for f, s in files.items():
    open(f, 'w').write(s)
print('edited', len(files), 'files')
