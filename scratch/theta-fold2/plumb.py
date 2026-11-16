"""theta-fold2 step 1 (plumbing, in place).

* theta-direct's UseForm.lean block (theta-split's `ThetaSplit.ThetaRatiosAtQM`, `Jmap_ne_zero`,
  `thetaPointOfFibre_of_qm_atQM`, verbatim, in namespace `HDec.HSyn.G0Split.ThetaPt.ThetaSplit`) moves into TailK right
  before `gluePieces_of_open4`; UseForm.lean is deleted and ThetaDirect/Split.lean imports TailZ19 instead.
* `gluePieces_of_open4` gets `hθ : PkgI1.QMHauptmodul → ThetaSplit.ThetaRatiosAtQM` and proves `thetaPoint` by
  `thetaPointOfFibre_of_qm_atQM (…) (hθ l.qmHauptmodul)`; `l.thetaRatiosAlgebraic` is no longer read.
* `sixContactMin_of_open4`, `_open6` … `_open15`, `_open17`, `_open18` take `hθ` and pass it on (the example after
  `_open6` gets the binder).
* TailZ25 imports `ZInQKernel.Contrib.OneProof.ThetaDirect` (whose import closure stops at TailZ24) and
  `sixContactMin_of_open19` passes `HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul`: its signature, and that of every
  later `sixContactMin_of_open*`, frozenTarget and the Contrib callers, are unchanged.
Run from the repository root."""
import re, os
H = 'ZInQKernel/OneProof/H/'
UF = 'ZInQKernel/Contrib/OneProof/ThetaDirect/UseForm.lean'
SP = 'ZInQKernel/Contrib/OneProof/ThetaDirect/Split.lean'
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

uf = open(UF).read().split('\n')
a = next(i for i, l in enumerate(uf) if l.startswith('/-! ### theta-fold: the use form'))
b = next(i for i, l in enumerate(uf) if l.startswith('end G0Split.ThetaPt.ThetaSplit'))
block = '\n'.join(uf[a:b + 1]).rstrip() + '\n\n'
assert block.count('def ThetaRatiosAtQM : Prop :=') == 1 and block.count('\ntheorem ') == 2
K = H + 'TailK.lean'
anchor = '/-- **Leaves.lean\'s `GluePieces` from leaf-fold4\'s open statements**'
sub1(K, anchor, block + anchor)
edit_decl(K, 'gluePieces_of_open4', [
    ('(l : OpenAddedLeaves4) (g : OpenGlue4) (hYu : QMLattice.YuB6Alg) : GluePieces :=',
     '(l : OpenAddedLeaves4) (g : OpenGlue4) (hYu : QMLattice.YuB6Alg)\n    ' + BINDER + ' : GluePieces :='),
    ('thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios', 'thetaPoint := G0Split.ThetaPt.ThetaSplit.thetaPointOfFibre_of_qm_atQM'),
    ('      l.thetaRatiosAlgebraic\n', '      (hθ l.qmHauptmodul)\n')])
edit_decl(K, 'sixContactMin_of_open4', [
    ('(hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=', '(hYu : QMLattice.YuB6Alg)\n    ' + BINDER + ' : ZInQ.SixContactMin :='),
    ('(gluePieces_of_open4 r t l g hYu) h20', '(gluePieces_of_open4 r t l g hYu hθ) h20')])

chain = [('TailO', 6), ('TailX', 7), ('TailZ4', 8), ('TailZ9', 9), ('TailZ11', 10), ('TailZ13', 11), ('TailZ15', 12),
         ('TailZ17', 13), ('TailZ18', 14), ('TailZ19', 15), ('TailZ23', 17), ('TailZ24', 18)]
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
# the supply point
Z25 = H + 'TailZ25.lean'
sub1(Z25, 'import ZInQKernel.Contrib.OneProof.EGAOpenImm\n',
     'import ZInQKernel.Contrib.OneProof.EGAOpenImm\nimport ZInQKernel.Contrib.OneProof.ThetaDirect\n')
edit_decl(Z25, 'sixContactMin_of_open19', [
    ('l g hYu h6 hSS hY3', 'l g hYu h6 hSS hY3\n    HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul')])
# the contributor copy goes
sub1(SP, 'import ZInQKernel.Contrib.OneProof.ThetaDirect.UseForm\n', 'import ZInQKernel.OneProof.H.TailZ19\n')
for f, s in files.items():
    open(f, 'w').write(s)
os.remove(UF)
print('edited', len(files), 'files; removed', UF)
